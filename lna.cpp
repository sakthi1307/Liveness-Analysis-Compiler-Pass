// This method implements what the pass does
//=============================================================================
// FILE:
//    LivenessAnalysis.cpp
//
// DESCRIPTION:
//    Visits all functions in a module, prints their names and the number of
//    arguments via stderr. Strictly speaking, this is an analysis pass (i.e.
//    the functions are not modified). However, in order to keep things simple
//    there's no 'print' method here (every analysis pass should implement it).
//
// USAGE:
//    New PM
//      opt -load-pass-plugin=libHelloWorld.dylib -passes="hello-world" `\`
//        -disable-output <input-llvm-file>
//
//
// License: MIT
//=============================================================================
#include "llvm/IR/Constant.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include <sstream>
#include <string>
#include <queue>
#include <unordered_set>
#include <unordered_map>

using namespace llvm;
using namespace std;

//-----------------------------------------------------------------------------
// LiveNess Analysis implementation
//-----------------------------------------------------------------------------
// No need to expose the internals of the pass to the outside world - keep
// everything in an anonymous namespace.
namespace
{

  string addrTag = ".addr";

  string removeDotAddr(string word)
  {
    size_t dotPos;
    if ((dotPos = word.find_first_of(".")) != string::npos)
    {
      return word.substr(0, dotPos);
    }
    return word;
  }

  // This method implements what the pass does
  void visitor(Function &F)
  {

    unordered_map<BasicBlock *, unordered_set<string>> LiveIn, UEvar, LiveOut, VarKill;
    for (auto &bb : F)
    {
      LiveIn[&bb] = unordered_set<string>();
      UEvar[&bb] = unordered_set<string>();
      LiveOut[&bb] = unordered_set<string>();
      VarKill[&bb] = unordered_set<string>();
    }
    // compute UEvar and VarKill
    for (auto &bb : F)
    {
      unordered_set<string> temp_vars;
      for (auto &i : bb)
      {
        if (i.getOpcode() == Instruction::Store)
        {

          string storeFrom = i.getOperand(0)->getName().str();
          // if constant, has no name
          if (storeFrom == "")
          {
            string s;
            raw_string_ostream rs(s);

            i.getOperand(0)->print(rs);
            Value *v = i.getOperand(0);
            if (isa<Constant>(v))
            {
              storeFrom = "constant";
            }
            else if (isa<Instruction>(v))
            {
              Instruction *v2 = cast<Instruction>(v);

              if (v2->getOpcode() == Instruction::Load)
              {
                storeFrom = removeDotAddr(v2->getOperand(0)->getName().str());
              }
            }
          }

          // storeTo is always a variable (never a constant)
          string storeTo = removeDotAddr(i.getOperand(1)->getName().str());
          if (storeFrom != "constant" && temp_vars.find(storeFrom) == temp_vars.end())
            UEvar[&bb].insert(storeFrom);

          VarKill[&bb].insert(storeTo);
          // localLiveOut.insert(storeTo);
        }

        if (i.isBinaryOp())
        {
          string opString;
          string op1, op2;

          // chedk if either operands are constants (constants have no names)
          op1 = i.getOperand(0)->getName().str();

          if (op1 == "")
          {
            string s;
            raw_string_ostream rs(s);

            Value *v = i.getOperand(0);
            if (isa<Constant>(v))
            {
              op1 = "constant";
            }
            else if (isa<Instruction>(v))
            {
              Instruction *v2 = cast<Instruction>(v);

              if (v2->getOpcode() == Instruction::Load)
              {
                op1 = removeDotAddr(v2->getOperand(0)->getName().str());
              }
            }
          }

          op2 = i.getOperand(1)->getName().str();
          if (op2 == "")
          {

            Value *v = i.getOperand(1);
            if (isa<Constant>(v))
            {
              op2 = "constant";
            }
            else if (isa<Instruction>(v))
            {
              Instruction *v2 = cast<Instruction>(v);

              if (v2->getOpcode() == Instruction::Load)
              {
                op2 = removeDotAddr(v2->getOperand(0)->getName().str());
              }
            }
          }
          // if the operand is not a constant and not in the temp_vars, add it to the UEvar
          if (op1 != "constant" && temp_vars.find(op1) == temp_vars.end() && VarKill[&bb].find(op1) == VarKill[&bb].end())
            UEvar[&bb].insert(op1);
          if (op2 != "constant" && temp_vars.find(op2) == temp_vars.end() && VarKill[&bb].find(op2) == VarKill[&bb].end())
            UEvar[&bb].insert(op2);

          string result = i.getName().str();
          if (VarKill[&bb].find(result) != VarKill[&bb].end())
          {
            UEvar[&bb].erase(result);
          }
          temp_vars.insert(result);
        }

        if (i.getOpcode() == Instruction::Load)
        {
          string loadFrom = removeDotAddr(i.getOperand(0)->getName().str());
          if (temp_vars.find(loadFrom) == temp_vars.end() && VarKill[&bb].find(loadFrom) == VarKill[&bb].end())
            UEvar[&bb].insert(loadFrom);
        }
      }
    }

    // compute LiveIn and LiveOut
    bool changed = true;
    while (changed)
    {
      changed = false;
      BasicBlock &bb = F.back();

      queue<BasicBlock *> workList;
      unordered_set<BasicBlock *> worklistSet;
      workList.push(&bb);
      while (workList.size() > 0)
      {
        BasicBlock *currentBB = workList.front();
        workList.pop();
        unordered_set<string> tempLiveIn;
        unordered_set<string> tempLiveOut;

        // compute LiveOut = U (Succ) LiveIn(Succ)
        for (auto succ : successors(currentBB))
        {
          for (auto var : LiveIn[succ])
          {
            tempLiveOut.insert(var);
          }
        }

        // compute LiveIn = UEvar U (LiveOut - VarKill)

        for (auto var : tempLiveOut)
        {
          tempLiveIn.insert(var);
        }
        for (auto var : VarKill[currentBB])
        {
          tempLiveIn.erase(var);
        }

        for (auto var : UEvar[currentBB])
        {
          tempLiveIn.insert(var);
        }

        // check if LiveOut has changed
        if (tempLiveOut != LiveOut[currentBB])
        {
          changed = true;
        }
        // update LiveIn and LiveOut
        LiveIn[currentBB] = tempLiveIn;
        LiveOut[currentBB] = tempLiveOut;

        // add predecessors to worklist
        for (auto pred : predecessors(currentBB))
        {
          if (worklistSet.find(pred) == worklistSet.end())
          {
            workList.push(pred);
            worklistSet.insert(pred);
          }
        }
      }
    }
    // print results
    for (auto &bb : F)
    {
      errs() << formatv("{0,-10}", "\n----") << formatv("{0,10}", bb.getName()) << formatv("{0,10}", "----\n");
      errs() << formatv("{0,-16}", "UEVar: ");
      for (auto var : UEvar[&bb])
      {
        errs() << var << " ";
      }
      errs() << "\n";
      errs() << formatv("{0,-16}", "VarKill: ");
      for (auto var : VarKill[&bb])
      {
        errs() << var << " ";
      }
      errs() << "\n";
      errs() << formatv("{0,-16}", "LiveOut: ");
      for (auto var : LiveOut[&bb])
      {
        errs() << var << " ";
      }
      errs() << "\n";
    }
  }
  // New PM implementation
  struct LivenessAnalysis : PassInfoMixin<LivenessAnalysis>
  {
    // Main entry point, takes IR unit to run the pass on (&F) and the
    // corresponding pass manager (to be queried if need be)
    PreservedAnalyses run(Function &F, FunctionAnalysisManager &)
    {
      visitor(F);
      return PreservedAnalyses::all();
    }

    // Without isRequired returning true, this pass will be skipped for functions
    // decorated with the optnone LLVM attribute. Note that clang -O0 decorates
    // all functions with optnone.
    static bool isRequired() { return true; }
  };
} // namespace

//-----------------------------------------------------------------------------
// New PM Registration
//-----------------------------------------------------------------------------
llvm::PassPluginLibraryInfo getLivenessAnalysisPluginInfo()
{
  return {LLVM_PLUGIN_API_VERSION, "LivenessAnalysis", LLVM_VERSION_STRING,
          [](PassBuilder &PB)
          {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, FunctionPassManager &FPM,
                   ArrayRef<PassBuilder::PipelineElement>)
                {
                  if (Name == "lna")
                  {
                    FPM.addPass(LivenessAnalysis());
                    return true;
                  }
                  return false;
                });
          }};
}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo()
{
  return getLivenessAnalysisPluginInfo();
}
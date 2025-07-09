//===-- LocalOpts.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/LocalOpts.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstrTypes.h"
// L'include seguente va in LocalOpts.h
#include <llvm/IR/Constants.h>

using namespace llvm;

/**
 * Esegue una verifica che l'istruzione sia ottimizzabile. Per "ottimizzabile" intendiamo che
 * contenga una variabile e una costante.
*/
bool optimizable(Instruction* instruction, ConstantInt* &constVal, Value* &opVal){
	for (auto op = instruction->op_begin(); op != instruction->op_end(); ++op) {
    if (dyn_cast<ConstantInt>(op))
      constVal = dyn_cast<ConstantInt>(op);
    else if (!opVal)
      opVal = *op;
  }

  if (constVal && opVal)
    return true;

  return false;
}

bool algebraicIdentity(llvm::BasicBlock::iterator &instruction){
  ConstantInt* constVal = nullptr;
  Value* opVal = nullptr;

  // Se l'istruzione non è ottimizzabile, esci.
  if(!optimizable(&*instruction, constVal, opVal)) return false;

  // Caso 1: somma
  if(instruction->getOpcode() == Instruction::Add){
    // Puntatore all'istruzione corrente.
    BinaryOperator *sum = dyn_cast<BinaryOperator>(instruction);

    /**
     * replaceAllUsesWith serve a sostituire il valore di X (come per esempio in X=Y+0)
     * col nuovo valore di Y. Di conseguenza, ogni volta che sarà chiamato X in realtà andrò
     * a rimpiazzarlo con Y.
     */
    if(constVal->getValue().isZero()){
      outs() << "Identità Algebrica [SUM]: " << *instruction << "\n";
      instruction++;
      sum->replaceAllUsesWith(opVal);
      sum->eraseFromParent();
      return true;
    }
  }
  // Caso 2: moltiplicazione
  else if(instruction->getOpcode() == Instruction::Mul) {
    // Puntatore all'istruzione corrente.
    BinaryOperator *mul = dyn_cast<BinaryOperator>(instruction);

    /**
     * replaceAllUsesWith serve a sostituire il valore di X (come per esempio in X=Y*1)
     * col nuovo valore di Y. Di conseguenza, ogni volta che sarà chiamato X in realtà andrò
     * a rimpiazzarlo con Y.
     */
    if(constVal->getValue().isOne()){
      outs() << "Identità Algebrica [MUL]: " << *instruction << "\n";
      instruction++;
      mul->replaceAllUsesWith(opVal);
      mul->eraseFromParent();
      return true;
    }
  }

  return false;
}

bool strengthReduction(llvm::BasicBlock::iterator &instruction) {
  ConstantInt* constVal = nullptr;
  Value* opVal = nullptr;

  // Se l'istruzione non è ottimizzabile, esci.
  if(!optimizable(&*instruction, constVal, opVal)) return false;

  // Casi generali: o è moltiplicazione o è divisione
  if((instruction->getOpcode() == Instruction::Mul) || (instruction->getOpcode() == Instruction::SDiv)){
    BinaryOperator *opSR = dyn_cast<BinaryOperator>(instruction);

    // Potenza di due precisa. Lo shift risulta molto più semplice.
    if (constVal->getValue().isPowerOf2()){
      // Calcolo dello shift con exactLogBase2 (poiché potenza di 2).
      ConstantInt *shift = ConstantInt::get(constVal->getType(), constVal->getValue().exactLogBase2());

      // Caso 1: moltiplicazione
      if(instruction->getOpcode() == Instruction::Mul) {
        outs() << "Strength Reduction [MUL] (pp): " << *instruction << "\n";
        Instruction *newShift = BinaryOperator::Create(BinaryOperator::Shl, opVal, shift);

        instruction++;
        newShift->insertAfter(opSR);
        opSR->replaceAllUsesWith(newShift);

        opSR->eraseFromParent();
        return true;
      }
      else if(instruction->getOpcode() == Instruction::SDiv) {
        outs() << "Strength Reduction [SDIV] (pp): " << *instruction << "\n";
        Instruction *newShift = BinaryOperator::Create(BinaryOperator::LShr, opVal, shift);

        instruction++;
        newShift->insertAfter(opSR);
        opSR->replaceAllUsesWith(newShift);

        opSR->eraseFromParent();
        return true;
      }
    }
    // Caso generale (non pp).
    else {
      // Cerco il logaritmo in base due più vicino per shiftare.
      ConstantInt *shift = ConstantInt::get(constVal->getType(), constVal->getValue().nearestLogBase2());
      bool add = false;

      APInt shiftValue = shift->getValue();
      uint32_t pow = 1;

      for (auto i = 0; i<shiftValue.getSExtValue(); i++)
        pow *= 2;

      uint32_t intConstValue = constVal->getValue().getSExtValue();
      uint32_t intCarryover;

      if(pow > intConstValue)
        intCarryover = pow - intConstValue;
      else {
        intCarryover = intConstValue - pow;
        add = true;
      }

      if(intCarryover == 1 && instruction->getOpcode() == Instruction::Mul) {
        Instruction *newShift = BinaryOperator::Create(BinaryOperator::Shl, opVal, shift);
        newShift -> insertAfter(opSR);

        Instruction *carryoverInstruction;
        if (add)
          carryoverInstruction = BinaryOperator::Create(BinaryOperator::Add, newShift, opVal);
        else
          carryoverInstruction = BinaryOperator::Create(BinaryOperator::Sub, newShift, opVal);

        outs() << "Strength Reduction [MUL]: " << *instruction << "\n";
        instruction++;
        carryoverInstruction->insertAfter(newShift);
        opSR->replaceAllUsesWith(carryoverInstruction);
        opSR->eraseFromParent();
        return true;
      }
    }
  }

  return false;
}

bool multiInstrOp(llvm::BasicBlock::iterator &instruction) {
  ConstantInt* constVal = nullptr;
  Value* opVal = nullptr;

  // Se l'istruzione non è ottimizzabile, esci.
  if(!optimizable(&*instruction, constVal, opVal)) return false;

  /**
   * Controlla che la variabile corrisponda effettivamente a una istruzione.
   * Nel caso, ad esempio, di una costante o una variabile globale (%b), non fa nulla.
  */
  Instruction *def = nullptr;
  if(!(def = dyn_cast<Instruction>(opVal))) return false;

  ConstantInt* defConstVal = nullptr;
  Value* defOpVal = nullptr;

  // Puntatore all'istruzione corrente.
  BinaryOperator *currInstr = dyn_cast<BinaryOperator>(instruction);

  switch(instruction->getOpcode()) {

    // a = b-1, c = a+1
    case Instruction::Add:
      if(def->getOpcode() == Instruction::Sub){
        if(ConstantInt* defConstVal = dyn_cast<ConstantInt>(def->getOperand(1))){
          if(constVal->getSExtValue() == defConstVal->getSExtValue()){
            outs() << "Multi Instruction Opt. [ADD/SUB]: " << *instruction << "\n";
            instruction++;
            currInstr->replaceAllUsesWith(def->getOperand(0));
            currInstr->eraseFromParent();
            return true;
          }
        }
      }
      break;

    // a = b+1, c = a-1
    case Instruction::Sub:
      if(def->getOpcode() == Instruction::Add){
        if(optimizable(def, defConstVal, defOpVal)){
          if(constVal->getSExtValue() == defConstVal->getSExtValue()){
            outs() << "Multi Instruction Opt. [SUB/ADD]: " << *instruction << "\n";
            instruction++;
            currInstr->replaceAllUsesWith(defOpVal);
            currInstr->eraseFromParent();
            return true;
          }
        }
      }
      break;

    // a = 5*b, c = a/5
    case Instruction::SDiv:
      if(def->getOpcode() == Instruction::Mul){
        if(optimizable(def, defConstVal, defOpVal)){
          if(constVal->getSExtValue() == defConstVal->getSExtValue()){
            outs() << "Multi Instruction Opt. [MUL/SDIV]: " << *instruction << "\n";
            instruction++;
            currInstr->replaceAllUsesWith(defOpVal);
            currInstr->eraseFromParent();
            return true;
          }
        }
      }
      break;

    // Default case
    default:
      break;

    return false;
  }
}

bool runOnBasicBlock(BasicBlock &BB) {
	llvm::BasicBlock::iterator instruction = BB.begin();
  while (instruction != BB.end()) {
    outs() << "ISTRUZIONE: " << *instruction << "\n";

    if(algebraicIdentity(instruction))
      continue;

    if(strengthReduction(instruction))
      continue;

    if(multiInstrOp(instruction))
      continue;
    
    instruction++;
  }

  return true;
}

bool runOnFunction(Function &F) {
  bool Transformed = false;

  for (auto Iter = F.begin(); Iter != F.end(); ++Iter) {
    if (runOnBasicBlock(*Iter)) {
      Transformed = true;
    }
  }

  return Transformed;
}

// METODO RUN
PreservedAnalyses LocalOpts::run(Module &M,
                                      ModuleAnalysisManager &AM) {
  for (auto Fiter = M.begin(); Fiter != M.end(); ++Fiter)
    if (runOnFunction(*Fiter))
      return PreservedAnalyses::none();
  
  return PreservedAnalyses::all();
}

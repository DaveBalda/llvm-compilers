#include "llvm/Transforms/Utils/LoopFusion.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/IR/TypedPointerType.h"

// Memorizzazione coppie di loop adiacenti
void pair(llvm::Loop* &L1, llvm::Loop* &L2, std::set<std::pair<llvm::Loop*, llvm::Loop*>> &set) {
  set.insert(std::make_pair(L1, L2));
}

/*
    Controlla che i loop siano adiacenti:
    - Se sono guarded, controlla che L2 postdomini L1
    - Se sono unguarded, controlla che l'exit block di L1 sia il preheader di L2
*/
void adjLoops(std::set<std::pair<llvm::Loop*, llvm::Loop*>> &adjacentLoops, llvm::LoopInfo &LI) {
  for (auto *L1 : LI) {
    for (auto *L2: LI) {
      if (L1->isGuarded() && L2->isGuarded()) {
        // Controlla che L2 postdomini L1
        if (L1->getExitBlock()->getSingleSuccessor() == L2->getLoopGuardBranch()->getParent()) {
          llvm::outs() << "Trovata coppia di loop guarded adiacenti!\n";
          pair(L1, L2, adjacentLoops);
        }
      }
      // Controlla che l'exit block di L1 sia il preheader di L2
      else {
        if (L1->getExitBlock() == L2->getLoopPreheader()) {
          llvm::outs() << "Trovata coppia di loop unguarded adiacenti!\n";
          pair(L1, L2, adjacentLoops);
        }
      }
    }
  }
}


// Verifica i loop dal punto di vista del control flow
bool checkEquivalence(std::pair<llvm::Loop*, llvm::Loop*> loop, llvm::DominatorTree &DT, llvm::PostDominatorTree &PDT) {

  // Verifica che i loop guarded abbiano la stessa condizione. Questo controllo non veniva fatto prima, ma è necessario per la fusione dei loop.
  if (loop.first->isGuarded()) 
    if (auto FC0CmpInst = llvm::dyn_cast<llvm::Instruction>(loop.first->getLoopGuardBranch()->getCondition()))
        if (auto FC1CmpInst = llvm::dyn_cast<llvm::Instruction>(loop.second->getLoopGuardBranch()->getCondition()))
          if (!FC0CmpInst->isIdenticalTo(FC1CmpInst))
            return 0;

  // Se i loop sono guarded, controlla che il guard di L1 domini il guard di L2 e viceversa (postdomini)
  if(loop.first->isGuarded()){
    if(DT.dominates(loop.first->getLoopGuardBranch()->getParent(), loop.second->getLoopGuardBranch()->getParent()) && PDT.dominates(loop.second->getLoopGuardBranch()->getParent(), loop.first->getLoopGuardBranch()->getParent())){
      llvm::outs() << "\nLoops control flow equivalent\n";
      return 1;
    }
  }
// Se i loop sono unguarded, controlla che il header di L1 domini il header di L2 e viceversa (postdomini)
  else {
    if (DT.dominates(loop.first->getHeader(), loop.second->getHeader()) && PDT.dominates(loop.second->getHeader(), loop.first->getHeader())) {
      llvm::outs() << "\nLoops control flow equivalent\n";
      return 1;
    }
  }
  return 0;
}


// Verifica del trip count
bool TripCount(std::pair<llvm::Loop*, llvm::Loop*> loop, llvm::ScalarEvolution &SE) {


  auto l1Backedges = SE.getBackedgeTakenCount(loop.first);
  auto l2Backedges = SE.getBackedgeTakenCount(loop.second);

  // Controllo aggiuntivo per evitare errori sulla SCEV (ScalarEvolution), per troppa complessità o per loop non standard
  if (l1Backedges->getSCEVType() == llvm::SCEVCouldNotCompute().getSCEVType() || 
    l2Backedges->getSCEVType() == llvm::SCEVCouldNotCompute().getSCEVType()) return 0;

  if (l1Backedges == l2Backedges) {
    llvm::outs() << "\nStesso numero di backedge\n";
    return 1;
  }
  return 0;
}


/*
    Funzione che controlla le negative dependecies di due loop:
    - Controllo che l'istruzione sia un array, cioè è un oggetto getelementptr.
    - Controllo gli usi dell'array es: A[i] --> I.getOperand(0) è A
    - Per ogni uso dell'array, recupero i suoi User, (nel secondo loop, per vedere se viene utilizzato) e inserisco all'interno
    di una variabile "inst", l'user trovato e poi verifico che sia nel secondo loop
    - Utilizziamo un'altra variabile "inst2" che contiene l'istruzione che rappresenta l'offset quindi "i+3" (quindi rappresenta a sua volta un'altra istruzione)
    - Tramite la variabile "PHIinst", prendo l'operando 0 (i+3 --> i) e controllo che l'operatore dell'"inst2" sia o un phinode o una sub, di conseguenza posso unire i due loop, altrimenti no.
*/
bool negDependencies(std::pair<llvm::Loop*, llvm::Loop*> loop) {

  // set con istruzioni dipedenti tra di loro
  std::set<llvm::Instruction*> depInst {};

  for (auto &BB : loop.first->getBlocks()) {
    for (llvm::Instruction &I : *BB) {
      // Controllo se l'istruzione è un array, cioè è un oggetto getelementptr
      if (I.getOpcode() == llvm::Instruction::GetElementPtr){

        // Controllo gli usi dell'array es: A[i] --> I.getOperand(0) è A
        for (auto &use : I.getOperand(0)->uses()) {
            //Per ogni uso dell'array, recupero i suoi User, (nel secondo loop, per vedere se viene utilizzato)
          if (auto inst = llvm::dyn_cast<llvm::Instruction>(use.getUser())) {
            // Controllo se l'istruzione è nel secondo loop, sempre A[i]
            if (loop.second->contains(inst)) {
              // Creo un'altra istruzione che contiene l'offset dell'array nel secondo loop, es: A[i+3] --> i+3
              if (auto inst2 = llvm::dyn_cast<llvm::Instruction>(inst->getOperand(1))) {
                // se l'istruzione non è una PHI, allora c'è un'altra istruzione che altera il valore dell'offset, es: i+3 --> i
                if (auto PHIinst = llvm::dyn_cast<llvm::Instruction>(inst2->getOperand(0))) {
                  switch(PHIinst->getOpcode()) {
                    case llvm::Instruction::PHI:
                    case llvm::Instruction::Sub: // se l'istruzione è una sub, l'offset è negativo e si riesce ad unire i loop
                      break;
                    default:
                      depInst.insert(PHIinst); // l'offset verrà modificato da un'altra istruzione --> i loop non possono essere uniti 
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  // visualizzazione, se presenti, delle istruzioni che violano la dipendenza negativa
  if (!depInst.empty()) {
    llvm::outs() << "\n\nLoop non fondibili a causa di violazioni sulla dipendenza negativa, a causa di:\n";
    for (auto inst : depInst) {
      llvm::outs() << "Istruzione: " << *inst << "\n";
    }
    return 0;
  }
  return 1;
}


// Fusione dei loop
void loopFusion(llvm::Loop* &L1, llvm::Loop* &L2){
 
  // sostituzione delle induction variables (variabile costante, che cambia in maniera costante all'interno del loop) di L2 con quelle di L1
  auto firstLoopIV = L1->getCanonicalInductionVariable();
  auto secondLoopIV = L2->getCanonicalInductionVariable();

  //
  secondLoopIV->replaceAllUsesWith(firstLoopIV);

  // modifiche al control flow graph

  auto header1 = L1->getHeader();
  auto header2 = L2->getHeader();
  auto latch1 = L1->getLoopLatch();
  auto latch2 = L2->getLoopLatch();
  auto exit = L2->getUniqueExitBlock();

  if (!L1->isGuarded()) {

    // modifiche al control flow graph eseguite:
    // header 1 --> exit L2 
    // body 1 --> body 2
    // body 2 --> latch 1
    // header 2 --> latch 2

    llvm::BasicBlock* lastL1BB = L1->getBlocks().drop_back(1).back();

    // collegamento body loop2 al body loop1
    lastL1BB->getTerminator()->setSuccessor(0, L2->getBlocks().drop_front(1).drop_back(1).front());

    // collegamento latch loop1 al body loop2
    L2->getBlocks().drop_front(1).drop_back(1).back()->getTerminator()->setSuccessor(0, latch1);

    // collegamento header loop2 al latch loop2
    llvm::BranchInst::Create(latch2, header2->getTerminator());
    header2->getTerminator()->eraseFromParent();

    // collegamento header loop1 all'L2 exit
    llvm::BranchInst::Create(L1->getBlocks().drop_front(1).front(), exit, header1->back().getOperand(0), header1->getTerminator());
    header1->getTerminator()->eraseFromParent();

  } else {

    // modifiche al control flow graph eseguite:
    // guard1 --> L2 exit
    // latch1 --> L2 exit
    // header1 --> header2
    // header2 --> latch1

    auto guard1 = L1->getLoopGuardBranch()->getParent();

    // collegamento guard loop1 all' L2 exit
    llvm::BranchInst::Create(L1->getLoopPreheader(), exit, guard1->back().getOperand(0), guard1->getTerminator());
    guard1->getTerminator()->eraseFromParent();

    // collegamento latch loop1 all'L2 exit
    llvm::BranchInst::Create(L1->getBlocks().front(), exit, latch1->back().getOperand(0), latch1->getTerminator());
    latch1->getTerminator()->eraseFromParent();

    // collegamento header loop1 all'header loop2
    L1->getBlocks().drop_back(1).back()->getTerminator()->setSuccessor(0, L2->getBlocks().front());

    // collegamento header loop2 al latch loop1
    L2->getBlocks().drop_back(1).back()->getTerminator()->setSuccessor(0, latch1);

    // rimozione header loop2 - PHI node
    header2->front().eraseFromParent();
  }
}


llvm::PreservedAnalyses llvm::LoopFusion::run(Function &F, FunctionAnalysisManager &AM) {

  llvm::LoopInfo &LI = AM.getResult<llvm::LoopAnalysis>(F);
  llvm::DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F);
  llvm::PostDominatorTree &PDT = AM.getResult<PostDominatorTreeAnalysis>(F);
  llvm::ScalarEvolution &SE = AM.getResult<ScalarEvolutionAnalysis>(F);
  
  // Set con coppie di loop adiacenti
  std::set<std::pair<llvm::Loop*, llvm::Loop*>> adjacentLoops {};
  
  adjLoops(adjacentLoops, LI);

  bool modified = 0;
  
  for (std::pair<llvm::Loop*, llvm::Loop*> loop : adjacentLoops) {
    if (!checkEquivalence(loop, DT, PDT)) continue;
    if (!TripCount(loop, SE)) continue;
    if (!negDependencies(loop)) continue;

    llvm::outs() << "\nI loop possono essere fusi\n";
    loopFusion(loop.first, loop.second);

    modified = 1;
  }

  if (modified) return llvm::PreservedAnalyses::none();
  else return llvm::PreservedAnalyses::all();
}
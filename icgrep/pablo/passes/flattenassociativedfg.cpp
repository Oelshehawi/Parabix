#include "flattenassociativedfg.h"

#include <pablo/codegenstate.h>
#include <pablo/optimizers/pablo_simplifier.hpp>
#include <boost/container/flat_map.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <pablo/analysis/pabloverifier.hpp>
#include <pablo/optimizers/distributivepass.h>


#include <pablo/printer_pablos.h>
#include <iostream>

using namespace boost;
using namespace boost::container;

namespace pablo {

using TypeId = PabloAST::ClassTypeId;
using Graph = adjacency_list<hash_setS, vecS, bidirectionalS, PabloAST *>;
using Map = flat_map<PabloAST *, Graph::vertex_descriptor>;

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief flatten
 ** ------------------------------------------------------------------------------------------------------------- */
inline void FlattenAssociativeDFG::flatten(Variadic * const var) {
    const TypeId typeId = var->getClassTypeId();
    for (unsigned i = 0; i < var->getNumOperands(); ) {
        PabloAST * const op = var->getOperand(i);
        if (op->getClassTypeId() == typeId) {
            var->removeOperand(i);
            for (unsigned j = 0; j != cast<Variadic>(op)->getNumOperands(); ++j) {
                var->addOperand(cast<Variadic>(op)->getOperand(j));
            }
            continue;
        }
        ++i;
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief applyNegationInwards
 *
 * Apply the De Morgans' law to any negated And or Or statement with the intent of further flattening its operands
 * and creating a bigger clause for the Simplifier to analyze.
 ** ------------------------------------------------------------------------------------------------------------- */
inline void FlattenAssociativeDFG::applyNegationInwards(Not * const var, PabloBlock * const block) {
    PabloAST * negatedVar = var->getOperand(0);
    if (isa<And>(negatedVar) || isa<Or>(negatedVar)) {
        Variadic * src = cast<Variadic>(negatedVar);
        const unsigned operands = src->getNumOperands();
        Variadic * replacement = nullptr;
        block->setInsertPoint(var->getPrevNode());
        if (isa<And>(negatedVar)) {
            replacement = block->createOr(operands, PabloBlock::createZeroes());
        } else {
            replacement = block->createAnd(operands, PabloBlock::createOnes());
        }
        block->setInsertPoint(replacement->getPrevNode());
        for (unsigned i = 0; i != operands; ++i) {
            replacement->setOperand(i, block->createNot(src->getOperand(i)));
        }
        flatten(replacement);
        var->replaceWith(replacement, true, true);
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief flatten
 ** ------------------------------------------------------------------------------------------------------------- */
void FlattenAssociativeDFG::flatten(PabloBlock * const block) {
    Statement * stmt = block->front();
    while (stmt) {
        Statement * next = stmt->getNextNode();
        if (isa<If>(stmt) || isa<While>(stmt)) {
            flatten(isa<If>(stmt) ? cast<If>(stmt)->getBody() : cast<While>(stmt)->getBody());
        } else if (isa<And>(stmt) || isa<Or>(stmt) || isa<Xor>(stmt)) {
            flatten(cast<Variadic>(stmt));
        } else if (isa<Not>(stmt)) {
            applyNegationInwards(cast<Not>(stmt), block);
        }
        stmt = next;
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief extractNegationsOutwards
 ** ------------------------------------------------------------------------------------------------------------- */
inline void FlattenAssociativeDFG::extractNegationsOutwards(Variadic * const var, PabloBlock * const block) {
    PabloAST * negated[var->getNumOperands()];
    unsigned operands = 0;
    for (unsigned i = 0; i != var->getNumOperands(); ) {
        if (isa<Not>(var->getOperand(i))) {
            negated[operands++] = cast<Not>(var->removeOperand(i))->getOperand(0);
            continue;
        }
        ++i;
    }
    if (operands) {
        block->setInsertPoint(var->getPrevNode());
        Variadic * extractedVar = nullptr;
        if (isa<And>(var)) {
            extractedVar = block->createOr(operands, PabloBlock::createZeroes());
        } else {
            extractedVar = block->createAnd(operands, PabloBlock::createOnes());
        }
        for (unsigned i = 0; i != operands; ++i) {
            extractedVar->setOperand(i, negated[i]);
        }
        std::sort(extractedVar->begin(), extractedVar->end());
        var->addOperand(block->createNot(extractedVar));
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief removeCommonLiterals
 ** ------------------------------------------------------------------------------------------------------------- */
inline void FlattenAssociativeDFG::removeCommonLiterals(Assign * const def) {
    PabloAST * op = def->getOperand(0);
    if (isa<And>(op) || isa<Or>(op) || isa<Xor>(op)) {
        removeCommonLiterals(def, cast<Variadic>(op));
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief removeCommonLiterals
 ** ------------------------------------------------------------------------------------------------------------- */
void FlattenAssociativeDFG::removeCommonLiterals(Statement * input, Variadic * var) {
    std::vector<PabloAST *> common(var->begin(), var->end());
    std::vector<PabloAST *> temp;
    temp.reserve(common.size());
    for (PabloAST * user : input->users()) {
        if (user->getClassTypeId() != var->getClassTypeId()) {
            if (isa<If>(user) && (input != cast<If>(user)->getCondition())) {
                continue;
            }
            return;
        }
        std::set_intersection(common.begin(), common.end(), cast<Variadic>(user)->begin(), cast<Variadic>(user)->end(), std::back_inserter(temp));
        common.swap(temp);
        temp.clear();
    }
    for (PabloAST * op : common) {
        var->removeOperand(op);
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief removeCommonLiterals
 ** ------------------------------------------------------------------------------------------------------------- */
inline void FlattenAssociativeDFG::removeCommonLiterals(PabloBlock * const block) {
    for (Statement * stmt : *block) {
        if (isa<If>(stmt) || isa<While>(stmt)) {
            removeCommonLiterals(isa<If>(stmt) ? cast<If>(stmt)->getBody() : cast<While>(stmt)->getBody());
        } else if (isa<And>(stmt) || isa<Or>(stmt)) {
            removeCommonLiterals(cast<Variadic>(stmt), cast<Variadic>(stmt));
        } else if (isa<Assign>(stmt)) {
            removeCommonLiterals(cast<Assign>(stmt));
        }
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief extract
 ** ------------------------------------------------------------------------------------------------------------- */
inline void FlattenAssociativeDFG::extract(PabloBlock * const block) {
    for (Statement * stmt : *block) {
        if (isa<If>(stmt) || isa<While>(stmt)) {
            extract(isa<If>(stmt) ? cast<If>(stmt)->getBody() : cast<While>(stmt)->getBody());
        } else if (isa<And>(stmt) || isa<Or>(stmt)) {
            extractNegationsOutwards(cast<Variadic>(stmt), block);
        }
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief process
 ** ------------------------------------------------------------------------------------------------------------- */
void FlattenAssociativeDFG::transform(PabloFunction & function) {

    for (;;) {

        FlattenAssociativeDFG::flatten(function.getEntryBlock());
        #ifndef NDEBUG
        PabloVerifier::verify(function, "post-flatten");
        #endif
        FlattenAssociativeDFG::removeCommonLiterals(function.getEntryBlock());
        #ifndef NDEBUG
        PabloVerifier::verify(function, "post-remove-common-literals");
        #endif

        Simplifier::optimize(function);

        const bool distributed = DistributivePass::optimize(function);

        FlattenAssociativeDFG::extract(function.getEntryBlock());
        #ifndef NDEBUG
        PabloVerifier::verify(function, "post-extract");
        #endif
        Simplifier::optimize(function);

        if (distributed == 0) {
            break;
        }
    }

    if (DistributivePass::optimize(function)) {
        throw std::runtime_error("Some distributions remained!");
    }

}

}

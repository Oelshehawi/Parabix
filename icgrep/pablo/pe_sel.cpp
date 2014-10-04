/*
 *  Copyright (c) 2014 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#include "pe_sel.h"
#include "pe_all.h"
#include "pe_and.h"
#include "pe_or.h"
#include "pe_not.h"

namespace pablo {

PabloE * makeSel(PabloE * if_expr, PabloE * t_expr, PabloE * f_expr) {
    if (All * all_if_expr = dyn_cast<All>(if_expr)) {
        if (all_if_expr->getValue()) {
            return t_expr;
        }
        else {
            return f_expr;
        }
    }
    else if (All * all_t_expr = dyn_cast<All>(t_expr)) {
        if (all_t_expr->getValue()) {
            return makeOr(if_expr, f_expr);
        }
        else {
            return makeAnd(makeNot(if_expr), f_expr);
        }
    }
    else if (All * all_f_expr = dyn_cast<All>(f_expr)) {
        if (all_f_expr->getValue()) {
            return makeOr(makeNot(if_expr), t_expr);
        }
        else {
            return makeAnd(if_expr, t_expr);
        }
    }
    else if (equals(t_expr, f_expr)) {
        return t_expr;
    }
    return new Sel(if_expr, t_expr, f_expr);
}

}

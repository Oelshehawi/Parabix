/*
 *  Copyright (c) 2014 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#ifndef PE_VAR_H
#define PE_VAR_H

#include <pablo/pe_pabloe.h>
#include <pablo/ps_assign.h>
#include <pablo/pe_string.h>

namespace pablo {

class Var : public PabloE {
    friend Var * makeVar(String *);
    friend Var * makeVar(Assign * assign);
    friend struct CodeGenState;
public:
    static inline bool classof(const PabloE * e) {
        return e->getClassTypeId() == ClassTypeId::Var;
    }
    static inline bool classof(const void *) {
        return false;
    }
    virtual ~Var(){
    }
    inline const std::string & getName() const {
        return *mVar;
    }
protected:
    Var(const PabloE * var)
    : PabloE(ClassTypeId::Var)
    , mVar(cast<String>(var)) {

    }
private:
    const String * const mVar;
};

inline Var * makeVar(String * var) {
    return new Var(var);
}

inline Var * makeVar(Assign * assign) {
    return new Var(assign->mName);
}

}



#endif // PE_VAR_H



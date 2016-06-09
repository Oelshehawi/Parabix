#ifndef DO_GREP_H
#define DO_GREP_H
/*
 *  Copyright (c) 2016 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#include <string>
#include <stdint.h>
#include <re/re_re.h>
#include <llvm/ExecutionEngine/ExecutionEngine.h>


namespace llvm { class raw_ostream; }



class GrepEngine {
    typedef void (*GrepFunctionType)(char * byte_data, size_t filesize, const int fileIdx, uint64_t finalLineUnterminated);
    typedef uint64_t (*GrepFunctionType_CountOnly)(char * byte_data, size_t filesize, const int fileIdx, uint64_t finalLineUnterminated);
public:

    GrepEngine() {}

    ~GrepEngine();
  
    void grepCodeGen(std::string moduleName, re::RE * re_ast, bool CountOnly, bool UTF_16 = false, bool isNameExpression = false);
    
    void doGrep(const std::string & fileName, const int fileIdx, bool CountOnly, std::vector<uint64_t> &total_CountOnly, bool UTF_16);
    
    re::CC *  grepCodepoints();
    
private:
   
    static bool finalLineIsUnterminated(const char * const fileBuffer, const size_t fileSize, bool UTF_16);

    GrepFunctionType mGrepFunction;
    GrepFunctionType_CountOnly mGrepFunction_CountOnly;

    bool mIsNameExpression;
    llvm::ExecutionEngine * mEngine;
};

void icgrep_Linking(Module * m, ExecutionEngine * e);


re::CC * getParsedCodePointSet();
void setParsedCodePointSet();

void initResult(std::vector<std::string> filenames);
void PrintResult(bool CountOnly, std::vector<uint64_t> & total_CountOnly);

#endif

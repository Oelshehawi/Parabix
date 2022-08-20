# Copyright (c) 2019 International Characters.
# This software is licensed to the public under the Open Software License 3.0.

# module: kernel.ztf

parabix_add_module(
NAME
    kernel.ztf
SRC
    common.cpp
    ztf-logic.cpp
    ztf-phrase-logic.cpp
    ztf-phrase-scan.cpp
DEPS
    kernel.basis
    kernel.io
    kernel.pipeline
    kernel.streamutils
    kernel.util
    toolchain
)

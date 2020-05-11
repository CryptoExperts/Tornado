#!/bin/bash

INLINING="-light-inline"
#INLINING="-inline-all -unroll"

# ACE bitslice
./usubac $INLINING -gen-bench -bits-per-reg 32 -B -no-sched -o nist/ace/usuba/bench/ace_ua_bitslice.c -arch std -no-share nist/ace/usuba/ua/ace_bitslice.ua
# ACE vslice
./usubac $INLINING -gen-bench -V -no-sched -o nist/ace/usuba/bench/ace_ua_vslice.c -arch std -no-share nist/ace/usuba/ua/ace.ua

# Ascon bitslice
./usubac -gen-bench $INLINING -bits-per-reg 32 -B -no-sched -o nist/ascon/usuba/bench/ascon_ua_bitslice.c -arch std -no-share nist/ascon/usuba/ua/ascon.ua
# Ascon vslice
./usubac -gen-bench $INLINING -V -no-sched -o nist/ascon/usuba/bench/ascon_ua_vslice.c -arch std -no-share nist/ascon/usuba/ua/ascon.ua

# GIFT bitslice
./usubac -gen-bench $INLINING -bits-per-reg 32 -B -no-sched -o nist/gift/usuba/bench/gift_ua_bitslice.c -arch std -no-share nist/gift/usuba/ua/gift_bitslice.ua
# GIFT bitslice
./usubac -gen-bench $INLINING -V -no-sched -o nist/gift/usuba/bench/gift_ua_vslice.c -arch std -no-share nist/gift/usuba/ua/gift.ua

# Gimli bitslice
./usubac -gen-bench $INLINING -bits-per-reg 32 -no-sched -B -o nist/gimli/usuba/bench/gimli_ua_bitslice.c nist/gimli/usuba/ua/gimli_bitslice.ua
# Gimli vslice
./usubac -gen-bench $INLINING -no-sched -V -o nist/gimli/usuba/bench/gimli_ua_vslice.c nist/gimli/usuba/ua/gimli.ua

# Photon bitslice
./usubac -gen-bench $INLINING -bits-per-reg 32 -B -no-sched -o nist/photon/usuba/bench/photon_ua_bitslice.c -arch std -no-share nist/photon/usuba/ua/photon_bitslice.ua
# Photon vslice (uses tables)
./usubac -gen-bench $INLINING -V -keep-tables -no-sched -o nist/photon/usuba/bench/photon_ua_vslice.c -arch std -no-share nist/photon/usuba/ua/photon_vslice.ua

# Pyjamask bitslice
./usubac -gen-bench $INLINING -bits-per-reg 32 -no-sched -B -o nist/pyjamask/usuba/bench/pyjamask_ua_bitslice.c -arch std -no-share nist/pyjamask/usuba/ua/pyjamask_bitslice.ua
# Pyjamask vslice
./usubac -gen-bench $INLINING -no-sched -V -o nist/pyjamask/usuba/bench/pyjamask_ua_vslice.c -arch std -no-share nist/pyjamask/usuba/ua/pyjamask_vslice.ua

# Skinny bitslice
./usubac -gen-bench $INLINING -bits-per-reg 32 -B -no-sched -o nist/skinny/usuba/bench/skinny_ua_bitslice.c -arch std -no-share nist/skinny/usuba/ua/skinny_bitslice.ua
# Skinny vslice (uses tables)
./usubac -gen-bench $INLINING -keep-tables -V -no-sched -o nist/skinny/usuba/bench/skinny_ua_vslice.c -arch std -no-share nist/skinny/usuba/ua/skinny_vslice.ua

# Clyde (spook) bitslice
./usubac -gen-bench $INLINING -bits-per-reg 32 -no-sched -B -o nist/clyde/usuba/bench/clyde_ua_bitslice.c nist/clyde/usuba/ua/clyde_bitslice.ua
# Clyde (spook) vslice
./usubac -gen-bench $INLINING -no-sched -V -o nist/clyde/usuba/bench/clyde_ua_vslice.c nist/clyde/usuba/ua/clyde.ua

# Spongent bitslice
./usubac -gen-bench $INLINING -bits-per-reg 32 -check-tbl -B -no-sched -o nist/spongent/usuba/bench/spongent_ua_bitslice.c -arch std -no-share nist/spongent/usuba/ua/spongent.ua

# Drygascon bitslice
./usubac -gen-bench $INLINING -bits-per-reg 32 -no-sched -B -o nist/drygascon/usuba/bench/drygascon_ua_bitslice.c nist/drygascon/usuba/ua/drygascon.ua
# Drygascon vslice
./usubac -gen-bench $INLINING -no-sched -V -o nist/drygascon/usuba/bench/drygascon_ua_vslice.c nist/drygascon/usuba/ua/drygascon.ua

# Subterranean bitslice
./usubac -gen-bench $INLINING -bits-per-reg 32 -no-sched -B -o nist/subterranean/usuba/bench/subterranean_ua_bitslice.c nist/subterranean/usuba/ua/subterranean.ua

# Xoodoo bitslice
./usubac -gen-bench $INLINING -bits-per-reg 32 -no-sched -B -o nist/xoodoo/usuba/bench/xoodoo_ua_bitslice.c nist/xoodoo/usuba/ua/xoodoo.ua
# Xoodoo vslice
./usubac -gen-bench $INLINING -no-sched -V -o nist/xoodoo/usuba/bench/xoodoo_ua_vslice.c nist/xoodoo/usuba/ua/xoodoo.ua

BUILD_DIR?=build
MINISATP_RELSYM?=-g
MINISATP_REL?=-std=c++11 -O3 -D NDEBUG
MINISATP_DEB?=-std=c++11 -O0 -D DEBUG 
MINISATP_PRF?=-std=c++11 -O3 -D NDEBUG
MINISATP_FPIC?=-fpic
MINISAT_INCLUDE?=-I/home/hadoop/cominisatps/include -I/home/hadoop/cominisatps/include/minisat
MINISAT_LIB?=-L/home/hadoop/cominisatps/lib -lminisat
MCL_INCLUDE?=
MCL_LIB?=
prefix?=/home/hadoop/cominisatps

**UWrMaxSat** is a quite new solver for MaxSAT and pseudo-Boolean problems. It has been created at the University of Wroclaw and can be characterized as a complete solver for partial weighted MaxSAT instances, and, independently, for linear pseudo-Boolean optimizing and decision ones.

When citing, always reference my [ICTAI 2020](https://www.ictai2020.org/) conference paper, bibtex record is [here](https://www.computer.org/csdl/api/v1/citation/bibtex/proceedings/1pP3sSVh3BS/922800a132).

Since the version 1.3 you can merge the power of this solver with the [SCIP solver](https:://scipopt.org), if you have a licence to use it (see: https://scipopt.org/index.php#license). The SCIP solver will be run in a separate thread, if a MaxSAT instance is not too big (less than 100000 variables and clauses). Using parameters, you can force the solver to ran in the same thread as UWrMaxSat for a given number of seconds and UWrMaxSat will be started afterwards.

Since the version 1.4 you can use the solver as a library with the IPAMIR interface (see [IPAMIR](https://maxsat-evaluations.github.io/2022/incremental.html)). Some UWrMaxSat parameters can be set in the environment variable UWRFLAGS, for example, UWRFLAGS="-v1 -scip-cpu=120". It works both with the library and with the standalone application.

================================================================================
### Quick Install

1. clone the repository into uwrmaxsat:  
    git clone https://github.com/marekpiotrow/UWrMaxSat uwrmaxsat

2. build the SAT solver:

    * 2.1 get COMiniSatPSChandrasekharDRUP.zip:  
        wget https://baldur.iti.kit.edu/sat-competition-2016/solvers/main/COMiniSatPSChandrasekharDRUP.zip  
    * 2.2 unzip and move:  
        unzip COMiniSatPSChandrasekharDRUP.zip  
        mv 'COMiniSatPS Chandrasekhar DRUP/cominisatps' .  
    * 2.3 apply uwrmaxsat/cominisatps.patch:  
        cd cominisatps  
        patch -p1 <../uwrmaxsat/cominisatps.patch  
    * 2.4 compile the SAT solver library:  
        cd simp  
        MROOT=.. make libr  
        cd ..  
        mkdir minisat ; cd minisat ; ln -s ../core ../simp ../mtl ../utils . ; cd ../..

3. build the MaxPre preprocessor (if you want to use it - see Comments below):  
    * 3.1 clone the MaxPre repository:  
        git clone https://github.com/Laakeri/maxpre  
    * 3.2 compile it as a static library:  
        cd maxpre  
        sed -i 's/-g/-D NDEBUG/' src/Makefile  
        make lib  
        cd ..

4. build the SCIP solver library (if you want to use it)  
    * 4.1 get sources of scipoptsuite from https://scipopt.org/index.php#download  
    * 4.2 untar and build a static library it:  
        tar zxvf scipoptsuite-8.1.0.tgz  
        cd scipoptsuite-8.1.0  
        sed -i "s/add_library(libscip/add_library(libscip STATIC/g" scip/src/CMakeLists.txt  
        mkdir build && cd build  
        cmake -DNO_EXTERNAL_CODE=on -DSOPLEX=on -DTPI=tny ..  
        make libscip  
        cd ../..  

5. build the UWrMaxSat solver (release version, statically linked):  
        cd uwrmaxsat  
        make config  
        make r
    * 5.1 replace the last command with the following one if you do not want to use MAXPRE and SCIP libraries:  
        MAXPRE= USESCIP=  make r  
    * 5.2 or with the one below if you do not want to use the MAXPRE library only:  
        MAXPRE=  make r  
    * 5.3 or with the one below if you do not want to use the SCIP library only:  
        USESCIP=  make r  

### Comments:

   - the executable file is: build/release/bin/uwrmaxsat

   - if you want to use unbounded weights in MaxSAT instances, remove # in config.mk in the first line 
     containing BIGWEIGHTS before running the last command

   - The program can be compiled with mingw64 g++ compiler in MSYS2 environment (https://www.msys2.org).

   - To build a dynamic library you have to compile the static libraries above with the compiler option -fPIC  
     and, in the last step, replace 'make r' with 'make lsh'. The compiler option can be added to the steps above  
     as follows:  
       (2) The SAT solver library should be made with the command: CFLAGS=-fPIC MROOT=.. make libr  
       (3) The MaxPre Makefile should be modified with: sed -i 's/-g/-fPIC -D NDEBUG/' src/Makefile  
       (4) At the beginning of scipoptsuite-8.1.0/scip/src/CMakeLists.txt the following line should be added:    
           set(SCIP_COMP_OPTIONS ${SCIP_COMP_OPTIONS} -fPIC)

### Other SAT solvers

You can replace COMiniSatPS SAT solver with (A) CaDiCaL by Armin Biere or (B) Glucose 4.1 by Gilles Audemard 
and Laurent Simon or (C) mergesat by Norbert Manthey - see steps 5(A) or 5(B) or 5(C) below.

* **5(A)** clone CaDiCaL and build UWrMaxSat with this SAT solver:  
    cd ..  
    git clone https://github.com/arminbiere/cadical  
    cd cadical  
    patch -p1 <../uwrmaxsat/cadical.patch  
    ./configure  
    make  
    cd ../uwrmaxsat  
    cp config.cadical config.mk  
    make clean  
    make r

* **5(B)** clone Glucose 4.1 and build UWrMaxSat with this SAT solver:  
    cd ..  
    wget https://www.labri.fr/perso/lsimon/downloads/softwares/glucose-syrup-4.1.tgz  
    tar zxvf glucose-syrup-4.1.tgz  
    cd glucose-syrup-4.1  
    patch -p1 <../uwrmaxsat/glucose4.1.patch  
    cd simp  
    MROOT=.. make libr  
    cd ..  
    mkdir minisat ; cd minisat ; ln -s ../core ../simp ../mtl ../utils . ; cd ../..  
    cd uwrmaxsat  
    cp config.glucose4 config.mk  
    make r

* **5(C)** clone mergesat and build UWrMaxSat with this SAT solver:  
    cd ..  
    git clone https://github.com/conp-solutions/mergesat  
    cd mergesat  
    make lr  
    cd ../uwrmaxsat  
    cp config.mergesat config.mk  
    make clean  
    make r


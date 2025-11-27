**UWrMaxSat** is a quite new solver for MaxSAT and pseudo-Boolean problems. It has been created at the University of Wroclaw and can be characterized as a complete solver for partial weighted MaxSAT instances, and, independently, for linear pseudo-Boolean optimizing and decision ones.

When citing, always reference my [ICTAI 2020](https://www.ictai2020.org/) conference paper, bibtex record is [here](https://www.computer.org/csdl/api/v1/citation/bibtex/proceedings/1pP3sSVh3BS/922800a132).

Since the version 1.3 you can merge the power of this solver with the [SCIP solver](https:://scipopt.org), if you have a licence to use it (see: https://scipopt.org/index.php#license). The SCIP solver will be run in a separate thread, if a MaxSAT instance is not too big (less than 100000 variables and clauses). Using parameters, you can force the solver to ran in the same thread as UWrMaxSat for a given number of seconds and UWrMaxSat will be started afterwards.

Since the version 1.4 you can use the solver as a library with the IPAMIR interface (see [IPAMIR](https://maxsat-evaluations.github.io/2022/incremental.html)). Some UWrMaxSat parameters can be set in the environment variable UWRFLAGS, for example, UWRFLAGS="-v1 -scip-cpu=120". It works both with the library and with the standalone application.

Since version 1.6.1 the IPAMIR library runs the SCIP solver in a separate thread in the similar way as the standalone application. This default behaviour can be changed by setting UWRFLAGS="-no-par".

Since version 1.7.0 the default SAT solver is changed to CaDiCaL by Armin Biere. 

================================================================================
### Quick Install

1. clone the repositories into uwrmaxsat and cominisatps:  
    git clone https://github.com/marekpiotrow/UWrMaxSat uwrmaxsat  
    git clone https://github.com/marekpiotrow/cominisatps  
    cd cominisatps  
    rm core simp mtl utils  
    ln -s minisat/core minisat/simp minisat/mtl minisat/utils .  
    cd ..  

2. clone and build the CaDiCaL SAT solver by Armin Biere:  
    git clone https://github.com/arminbiere/cadical  
    cd cadical  
    git checkout rel-2.2.0-backports  
    patch -p1 <../uwrmaxsat/cadical.patch  
    ./configure --no-contracts --no-tracing  
    make cadical  
    cd ../uwrmaxsat  
    cp config.cadical config.mk  
    cd ..  

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
        tar zxf scipoptsuite-9.2.4.tgz  
        cd scipoptsuite-9.2.4  
        mkdir build && cd build  
        cmake -DSYM=nauty -DSHARED=off -DNO_EXTERNAL_CODE=on -DSOPLEX=on -DGMP=on -DMPFR=on -DBOOST=on -DTPI=tny ..  
        cmake --build . --config Release --target libscip libsoplex-pic  
        cd ../..  

5. build the UWrMaxSat solver (release version, statically linked):  
        cd uwrmaxsat  
        make clean    
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
       (2) The SAT solver library should be configured with the command: CXXFLAGS=-fPIC ./configure  
       (3) The MaxPre Makefile should be modified with: sed -i 's/-g/-fPIC -D NDEBUG/' src/Makefile  
       (4) Add the following option to the first line starting with cmake:    
           -DSCIP_COMP_OPTIONS=-fPIC  

### Other SAT solvers

You can replace CaDiCaL SAT solver with (A) COMiniSatPS by Chanseok Oh or (B) Glucose 4.1 by Gilles Audemard 
and Laurent Simon or (C) mergesat by Norbert Manthey - see steps 5(A) or 5(B) or 5(C) below.

* **5(A)** clone COMiniSatPS and build UWrMaxSat with this SAT solver:  
    git clone https://github.com/marekpiotrow/cominisatps  
    cd cominisatps  
    rm core simp mtl utils && ln -s minisat/core minisat/simp minisat/mtl minisat/utils .  
    make lr  
    cd ../uwrmaxsat  
    cp config.cominisatps config.mk  
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
    mkdir minisat ; cd minisat ; ln -s ../core ../simp ../mtl ../utils . ; cd ..  
    cd ../uwrmaxsat  
    cp config.glucose4 config.mk  
    make clean  
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


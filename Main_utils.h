
extern bool   opt_model_out;
extern bool   opt_bin_model_out;
extern bool   opt_satisfiable_out;

extern bool   opt_preprocess;
extern bool   opt_old_format;
extern int    opt_mem_lim;
extern bool   opt_use_maxpre;

#ifdef MAXPRE
extern char  *opt_maxpre_str;
extern int    opt_maxpre_time;
extern int    opt_maxpre_skip;
#endif

#ifdef USE_SCIP
extern bool   opt_use_scip_slvr;
extern double opt_scip_cpu;
extern double opt_scip_cpu_default;
extern bool   opt_scip_parallel;
extern time_t wall_clock_time;
#endif

extern MsSolver *pb_solver;

void reportf(const char* format, ...);
void SIGINT_handler(int /*signum*/);
void SIGTERM_handler(int signum);
void increase_stack_size(int new_size);
PbSolver::solve_Command convert(Command cmd);


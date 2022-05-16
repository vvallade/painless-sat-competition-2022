#ifndef _application_h_INCLUDED
#define _application_h_INCLUDED

#include "internal.h"

struct kissat;

#include "parse.h"

typedef struct application application;
struct application
{
    struct kissat *solver;
    const char *input_path;
#ifndef NPROOFS
    const char *proof_path;
    file proof_file;
    bool force;
    int binary;
#endif
    int time;
    int conflicts;
    int decisions;
    strictness strict;
    bool partial;
    bool witness;
    int max_var;
};

void init_app(application *application, struct kissat *solver);

bool write_proof(application *application);
void close_proof(application *application);

#ifndef NOPTIONS
void print_options(struct kissat *solver);
#endif

void print_limits(application *application);

bool parse_input(application *application);

bool parse_options(application *application, int argc, char **argv);

bool parsed_one_option_and_return_zero_exit_code(char *arg);

void setHeuristic(kissat *solver, bool vsids);

void setSharingClauseFunctions(kissat *solver, void *issuer, ExportClause exp, ImportUnitClause impUnit, ImportClause imp);

int kissat_application(struct kissat *, int argc, char **argv);

#endif

// -----------------------------------------------------------------------------
// Copyright (C) 2022  AK
//
// This file is part of PaInleSS.
//
// PaInleSS is free software: you can redistribute it and/or modify it under the
// terms of the GNU General Public License as published by the Free Software
// Foundation, either version 3 of the License, or (at your option) any later
// version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
// FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
// details.
//
// You should have received a copy of the GNU General Public License along with
// this program.  If not, see <http://www.gnu.org/licenses/>.
// -----------------------------------------------------------------------------

// Kissat includes
#include "../solvers/Kissat.h"
#include "../kissat/src/print.h"
#include "../kissat/src/witness.h"
#include "../kissat/src/inline.h"
#include "../kissat/src/literal.h"

#include "../utils/Logger.h"
#include "../utils/System.h"
#include "../utils/Parameters.h"
#include "../clauses/ClauseManager.h"

void kissatExportClause(void *issuer, int lbd, std::vector<int> &cls)
{
    Kissat *kp = (Kissat *)issuer;

    if (lbd > kp->lbdLimit)
        return;

    ClauseExchange *ncls = ClauseManager::allocClause(cls.size());

    ncls->lbd = lbd;
    // printf("K[%d] ",kp->id);
    for (unsigned i = 0; i < cls.size(); i++){
        ncls->lits[i] = cls[i];
        // printf("%d ",cls[i]);
    }
    // printf("\n");

    ncls->from = kp->id;
    kp->exportClauses++;

    kp->clausesToExport.addClause(ncls);
}

int kissatImportUnit(void *issuer)
{
    Kissat *kp = (Kissat *)issuer;

    int l = 0;

    ClauseExchange *cls = NULL;

    if (kp->unitsToImport.getClause(&cls) == false)
        return l;

    // while (kp->k_application.max_var < abs(cls->lits[0]))
    //     assert(0);

    l = cls->lits[0];

    ClauseManager::releaseClause(cls);

    return l;
}

bool kissatImportClause(void *issuer, unsigned *lbd, std::vector<int> &kcls)
{
    Kissat *kp = (Kissat *)issuer;

    ClauseExchange *cls = NULL;
    kcls.clear();

    if (kp->clausesToImport.getClause(&cls) == false)
        return false;

    for (int i = 0; i < cls->size; i++)
    {
        // while (kp->k_application.max_var < variable)
        // assert(0);
        kcls.push_back(cls->lits[i]);
    }

    *lbd = cls->lbd;

    ClauseManager::releaseClause(cls);
    return true;
}

Kissat::Kissat(int id) : SolverInterface(id, KISSAT), exportClauses(0)
{
    lbdLimit = Parameters::getIntParam("lbd-limit", 2);

    solver = kissat_init();

    setSharingClauseFunctions(solver, this, &kissatExportClause, &kissatImportUnit, &kissatImportClause);
}

Kissat::~Kissat()
{
    // kissat_release(solver);
    // delete solver;
}

bool Kissat::loadFormula(const char *filename)
{
    int argc = 2;
    char *argv[2];
    argv[1] = strdup(filename);
    // strcpy(argv[1], filename);
    if (argc == 2)
        if (parsed_one_option_and_return_zero_exit_code(argv[1]))
            return false;
    init_app(&k_application, solver);

    if (!parse_options(&k_application, argc, argv))
        return true;

#ifndef NPROOFS
    if (!write_proof(&k_application))
        return true;
#endif
    if (!parse_input(&k_application))
    {
#ifndef NPROOFS
        close_proof(&k_application);
#endif
        return true;
    }
#ifndef QUIET
#ifndef NOPTIONS
    print_options(solver);
#endif
    print_limits(&k_application);
    kissat_section(solver, "solving");
#endif
    return true;
}

// Get the number of variables of the formula
int Kissat::getVariablesCount()
{
    return solver->vars;
}

// Get a variable suitable for search splitting
int Kissat::getDivisionVariable()
{
    return (rand() % getVariablesCount()) + 1;
}

// Set initial phase for a given variable
void Kissat::setPhase(const int var, const bool phase)
{
    setPolarity(solver, var, phase ? 1 : -1);
}

// Bump activity for a given variable
void Kissat::bumpVariableActivity(const int var, const int times)
{
}

// Interrupt the SAT solving, so it can be started again with new assumptions
void Kissat::setSolverInterrupt()
{
    stopSolver = true;
    // kissat_interrupt(solver);
}

void Kissat::unsetSolverInterrupt()
{
    stopSolver = false;
    // clearInterrupt(solver);
}

// Diversify the solver
void Kissat::diversify(int id)
{
    // if (id == ID_XOR)
    //     solver->GE = true;
    // else
    //     solver->GE = false;

    // if (id % 4 >= 2)
    //     solver->verso = false;
    // else
    //     solver->verso = true;
    if (id % 2)
        setHeuristic(solver, false);
    else
        setHeuristic(solver, true);
}

// Solve the formula with a given set of assumptions
// return 10 for SAT, 20 for UNSAT, 0 for UNKNOWN
SatResult Kissat::solve(const std::vector<int> &cube)
{
    unsetSolverInterrupt();
    if (cube.size() > 0)
        printf("kissat cube not emptu\n");
    // std::vector<ClauseExchange *> tmp;

    // tmp.clear();
    // clausesToAdd.getClauses(tmp);

    // for (size_t ind = 0; ind < tmp.size(); ind++)
    // {
    //     vec<Lit> mcls;

    //     for (int i = 0; i < tmp[ind]->size; i++)
    //     {
    //         int lit = tmp[ind]->lits[i];
    //         int var = abs(lit);

    //         while (var > solver->nVars())
    //             solver->newVar(true, false);

    //         mcls.push(MINI_LIT(lit));
    //     }

    //     ClauseManager::releaseClause(tmp[ind]);

    //     if (solver->addClause(mcls) == false)
    //     {
    //         return UNSAT;
    //     }
    // }
    int res = kissat_solve(solver);
    // printf("c [%d] Kissat: %d exported CONFLICT clauses\n", id, exportClauses);

#ifndef NPROOFS
    close_proof(&k_application);
#endif

    if (res)
    {
        if (res == UNSAT)
            return UNSAT;
        else if (res == SAT)
            return SAT;
    }

    return UNKNOWN;
}

void Kissat::addClause(ClauseExchange *clause)
{
    clausesToAdd.addClause(clause);
    setSolverInterrupt();
}

void Kissat::addLearnedClause(ClauseExchange *clause)
{
    if (clause->size == 1)
        unitsToImport.addClause(clause);
    else
        clausesToImport.addClause(clause);
}

void Kissat::addClauses(const std::vector<ClauseExchange *> &clauses)
{
    clausesToAdd.addClauses(clauses);

    setSolverInterrupt();
}

void Kissat::addInitialClauses(const std::vector<ClauseExchange *> &clauses)
{
    // kissat_reserve(solver, variables);
}

void Kissat::addLearnedClauses(const std::vector<ClauseExchange *> &clauses)
{
    for (size_t i = 0; i < clauses.size(); i++)
        addLearnedClause(clauses[i]);
}

void Kissat::getLearnedClauses(std::vector<ClauseExchange *> &clauses)
{
    clausesToExport.getClauses(clauses);
}

void Kissat::increaseClauseProduction()
{
    lbdLimit++;
}

void Kissat::decreaseClauseProduction()
{
    if (lbdLimit > 2)
        lbdLimit--;
}

SolvingStatistics Kissat::getStatistics()
{
    SolvingStatistics stats;
    statistics *statistics = &solver->statistics;

    stats.conflicts = get_conflict(solver);
    stats.propagations = get_propagation(solver);
    stats.restarts = get_restart(solver);
    stats.decisions = get_decision(solver);
    stats.memPeak = get_memory();

    return stats;
}

std::vector<int> Kissat::getModel()
{
    std::vector<int> model;

    for (int eidx = 1; eidx <= k_application.max_var; eidx++)
    {
        int tmp = kissat_value(solver, eidx);
        if (!tmp && !k_application.partial)
            tmp = eidx;
        if (tmp)
            model.push_back(tmp);
    }
    return model;
}

vector<int> Kissat::getFinalAnalysis()
{
    vector<int> outCls;

    //    for (int i = 0; i < solver->conflict.size(); i++) {
    //       outCls.push_back(INT_LIT(solver->conflict[i]));
    //    }

    return outCls;
}

vector<int> Kissat::getSatAssumptions()
{
    vector<int> outCls;
    // vec<Lit> lits;
    // solver->getAssumptions(lits);
    // for (int i = 0; i < lits.size(); i++)
    // {
    //     outCls.push_back(-(INT_LIT(lits[i])));
    // }
    return outCls;
};

void Kissat::setStrengthening(bool b)
{
    // solver->setStrengthening(b);
}

#include "analyze.h"
#include "decide.h"
#include "eliminate.h"
#include "internal.h"
#include "logging.h"
#include "print.h"
#include "probe.h"
#include "propsearch.h"
#include "search.h"
#include "reduce.h"
#include "reluctant.h"
#include "report.h"
#include "restart.h"
#include "terminate.h"
#include "trail.h"
#include "walk.h"
#include "import.h"
#include "learn.h"
#include "inline.h"

#include <inttypes.h>

static void
start_search(kissat *solver)
{
  START(search);
  INC(searches);

  REPORT(0, '*');

  bool stable = (GET_OPTION(stable) == 2);

  solver->stable = stable;
  kissat_phase(solver, "search", GET(searches),
               "initializing %s search after %" PRIu64 " conflicts",
               (stable ? "stable" : "focus"), CONFLICTS);

  kissat_init_averages(solver, &AVERAGES);

  if (solver->stable)
    kissat_init_reluctant(solver);

  kissat_init_limits(solver);

  unsigned seed = GET_OPTION(seed);
  solver->random = seed;
  LOG("initialized random number generator with seed %u", seed);

  kissat_reset_rephased(solver);

  const unsigned eagersubsume = GET_OPTION(eagersubsume);
  if (eagersubsume && !solver->clueue.elements)
    kissat_init_clueue(solver, &solver->clueue, eagersubsume);
#ifndef QUIET
  limits *limits = &solver->limits;
  limited *limited = &solver->limited;
  if (!limited->conflicts && !limited->decisions)
    kissat_very_verbose(solver, "starting unlimited search");
  else if (limited->conflicts && !limited->decisions)
    kissat_very_verbose(solver,
                        "starting search with conflicts limited to %" PRIu64,
                        limits->conflicts);
  else if (!limited->conflicts && limited->decisions)
    kissat_very_verbose(solver,
                        "starting search with decisions limited to %" PRIu64,
                        limits->decisions);
  else
    kissat_very_verbose(solver,
                        "starting search with decisions limited to %" PRIu64
                        " and conflicts limited to %" PRIu64,
                        limits->decisions, limits->conflicts);
  if (stable)
  {
    START(stable);
    REPORT(0, '[');
  }
  else
  {
    START(focused);
    REPORT(0, '{');
  }
#endif
}

static void
stop_search(kissat *solver, int res)
{
  if (solver->limited.conflicts)
  {
    LOG("reset conflict limit");
    solver->limited.conflicts = false;
  }

  if (solver->limited.decisions)
  {
    LOG("reset decision limit");
    solver->limited.decisions = false;
  }

  if (solver->terminate)
  {
    kissat_very_verbose(solver, "termination forced externally");
    solver->terminate = 0;
  }

#ifndef QUIET
  LOG("search result %d", res);
  if (solver->stable)
  {
    REPORT(0, ']');
    STOP(stable);
    solver->stable = false;
  }
  else
  {
    REPORT(0, '}');
    STOP(focused);
  }
  char type = (res == 10 ? '1' : res == 20 ? '0'
                                           : '?');
  REPORT(0, type);
#else
  (void)res;
#endif

  STOP(search);
}

static void
iterate(kissat *solver)
{
  assert(solver->iterating);
  solver->iterating = false;
  REPORT(0, 'i');
}

static bool
conflict_limit_hit(kissat *solver)
{
  if (!solver->limited.conflicts)
    return false;
  if (solver->limits.conflicts > solver->statistics.conflicts)
    return false;
  kissat_very_verbose(solver, "conflict limit %" PRIu64 " hit after %" PRIu64 " conflicts",
                      solver->limits.conflicts,
                      solver->statistics.conflicts);
  return true;
}

static bool
decision_limit_hit(kissat *solver)
{
  if (!solver->limited.decisions)
    return false;
  if (solver->limits.decisions > solver->statistics.decisions)
    return false;
  kissat_very_verbose(solver, "decision limit %" PRIu64 " hit after %" PRIu64 " decisions",
                      solver->limits.decisions,
                      solver->statistics.decisions);
  return true;
}

void importUnitClauses(kissat *solver)
{
  assert(solver->level == 0);

  if (solver->importUnitCallback == NULL)
    return;

  int elit = 0;
  while ((elit = solver->importUnitCallback(solver->issuer)) != 0)
  {
    const unsigned l = kissat_import_literal(solver, elit);
    if (!VALID_INTERNAL_LITERAL(l))
      continue;
    if (VALUE(l) == 0)
    {
      if (!ACTIVE(IDX(l)))
        continue;
      unsigned unit_cls[1] = {l};
      ADD_UNCHECKED_INTERNAL(1, unit_cls);
      kissat_assign_unit(solver, l);
      solver->iterating = true;
      CHECK_AND_ADD_UNIT(l);
      ADD_UNIT_TO_PROOF(l);
    }
  }
}

unsigned importClauses(kissat *solver)
{
  assert(solver->level == 0);

  if (solver->importClauseCallback == NULL)
    return 0;
  std::vector<int> importedClause;
  unsigned glue = 0;
  unsigned size = 0;

  while (solver->importClauseCallback(solver->issuer, &glue, importedClause))
  {
    clause *c = NULL;
    size = importedClause.size();
    assert(size > 1);
    bool do_not_import = false;
    unsigned lits[size];

    for (size_t i = 0; i < size; i++)
    {
      unsigned val = kissat_import_literal(solver, importedClause[i]);
      if (!VALID_INTERNAL_LITERAL(val))
      {
        do_not_import = true;
        break;
      }
      lits[i] = val;
    }
    if (do_not_import)
    {
      importedClause.clear();
      continue;
    }
    kissat_sort_literals(solver, size, lits);
    unsigned cpt = 0;
    unsigned ind = 0;
    bool stop = true;
    for (size_t i = 0; i < size; i++)
    {
      unsigned lit = lits[i];
      if (VALUE(lit) < 0)
      {
        cpt++;
        stop = false;
      }
      else if (VALUE(lit) == 0)
      {
        ind = i;
        stop = false;
      }
      flags *f = FLAGS(IDX(lit));
      if (!f->active)
      {
        stop = true;
        break;
      }
      // printf("%d(%d)[%d] ", lit, kissat_export_literal(solver, lit), VALUE(lit));
    }
    // printf("\n");
    if (stop)
    {
      importedClause.clear();
      continue;
    }

    if (cpt == (size - 1))
    {
      unsigned tmp = lits[0];
      lits[0] = lits[ind];
      lits[ind] = tmp;
    }
    if (cpt == size)
    {
      printf("c imported clause UNSAT !\n");
      return 20;
    }

    ADD_UNCHECKED_INTERNAL(size, lits);

    reference ref = new_imported_clause(solver, false, glue, size, lits);

    if (size == 2)
    {
      assert(ref == INVALID_REF);
      if (VALUE(lits[0]) == 0 && VALUE(lits[1]) < 0)
        kissat_assign_binary(solver, false, lits[0], lits[1]);
    }
    else
    {
      assert(ref != INVALID_REF);

      clause *c = kissat_dereference_clause(solver, ref);
      const unsigned tier2 = (unsigned)GET_OPTION(tier2);
      c->used = 1 + (glue <= tier2);
      if (cpt == (size - 1))
      {
        if (VALUE(lits[0]) == 0)
          // kissat_assign(solver, lits[0], 2, false, 0, ref);
          kissat_assign_reference(solver, lits[0], ref, c);
      }
    }
    importedClause.clear();
  }
  return 0;
}

int kissat_search(kissat *solver)
{
  start_search(solver);

  int res = 0;//kissat_walk_initially(solver);

  while (!res)
  {
    if (solver->level == 0)
    {
      importUnitClauses(solver);
      res = importClauses(solver);
      if (res == 20)
        break;
    }

    clause *conflict = kissat_search_propagate(solver);

    if (conflict)
    {
      res = kissat_analyze(solver, conflict);
    }
    else if (solver->iterating)
      iterate(solver);
    else if (!solver->unassigned)
      res = 10;
    else if (TERMINATED(11))
      break;
    else if (conflict_limit_hit(solver))
      break;
    else if (kissat_reducing(solver))
      res = kissat_reduce(solver);
    else if (kissat_restarting(solver))
      kissat_restart(solver);
    else if (kissat_rephasing(solver))
      kissat_rephase(solver);
    else if (kissat_eliminating(solver))
      res = kissat_eliminate(solver);
    else if (kissat_probing(solver))
      res = kissat_probe(solver);
    else if (!solver->level && solver->unflushed)
      kissat_flush_trail(solver);
    else if (decision_limit_hit(solver))
      break;
    else
      kissat_decide(solver);
  }

  stop_search(solver, res);

  return res;
}

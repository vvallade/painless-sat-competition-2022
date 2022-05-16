#include "allocate.h"
#include "backtrack.h"
#include "error.h"
#include "search.h"
#include "import.h"
#include "inline.h"
#include "print.h"
#include "propsearch.h"
#include "require.h"
#include "resize.h"
#include "resources.h"
#include "phases.h"

#include <assert.h>
#include <inttypes.h>
#include <limits.h>
#include <stdlib.h>
#include <stdio.h>

kissat *
kissat_init(void)
{
  kissat *solver = (kissat *)kissat_calloc(0, 1, sizeof *solver);
#ifndef NOPTIONS
  kissat_init_options(&solver->options);
#else
  kissat_init_options();
#endif
#ifndef QUIET
  kissat_init_profiles(&solver->profiles);
#endif
  START(total);
  kissat_init_queue(&solver->queue);
  kissat_push_frame(solver, INVALID_LIT);
  solver->watching = true;
  solver->conflict.size = 2;
  solver->conflict.keep = true;
  solver->scinc = 1.0;
  solver->first_reducible = INVALID_REF;
  solver->last_irredundant = INVALID_REF;
  // CHB
  solver->step_dec_chb = 0.000001;
  solver->step_min_chb = 0.06;
  // MAB
  solver->mab_heuristics = 2;
  solver->mab_decisions = 0;
  solver->mab_chosen_tot = 0;
#ifndef NDEBUG
  kissat_init_checker(solver);
#endif
  /// ADDED
  solver->asynch_interrupt = false;
  solver->issuer = NULL;
  solver->exportClauseCallback = NULL;
  solver->importUnitCallback = NULL;
  solver->importClauseCallback = NULL;

  return solver;
}

#define DEALLOC_GENERIC(NAME, ELEMENTS_PER_BLOCK)                        \
  do                                                                     \
  {                                                                      \
    const size_t block_size = ELEMENTS_PER_BLOCK * sizeof *solver->NAME; \
    kissat_dealloc(solver, solver->NAME, solver->size, block_size);      \
    solver->NAME = 0;                                                    \
  } while (0)

#define DEALLOC_VARIABLE_INDEXED(NAME) \
  DEALLOC_GENERIC(NAME, 1)

#define DEALLOC_LITERAL_INDEXED(NAME) \
  DEALLOC_GENERIC(NAME, 2)

#define RELEASE_LITERAL_INDEXED_STACKS(NAME, ACCESS)     \
  do                                                     \
  {                                                      \
    for (all_stack(unsigned, IDX_RILIS, solver->active)) \
    {                                                    \
      const unsigned LIT_RILIS = LIT(IDX_RILIS);         \
      const unsigned NOT_LIT_RILIS = NOT(LIT_RILIS);     \
      RELEASE_STACK(ACCESS(LIT_RILIS));                  \
      RELEASE_STACK(ACCESS(NOT_LIT_RILIS));              \
    }                                                    \
    DEALLOC_LITERAL_INDEXED(NAME);                       \
  } while (0)

void kissat_release(kissat *solver)
{
  kissat_require_initialized(solver);

  kissat_release_heap(solver, &solver->scores);

  // CHB
  kissat_release_heap(solver, &solver->scores_chb);
  DEALLOC_VARIABLE_INDEXED(conflicted_chb);

  kissat_release_heap(solver, &solver->schedule);

  kissat_release_clueue(solver, &solver->clueue);

  RELEASE_STACK(solver->exportk);
  RELEASE_STACK(solver->import);

  DEALLOC_VARIABLE_INDEXED(assigned);
  DEALLOC_VARIABLE_INDEXED(flags);
  DEALLOC_VARIABLE_INDEXED(links);
  DEALLOC_VARIABLE_INDEXED(phases);

  DEALLOC_LITERAL_INDEXED(marks);
  DEALLOC_LITERAL_INDEXED(values);
  DEALLOC_LITERAL_INDEXED(watches);

  RELEASE_STACK(solver->import);
  RELEASE_STACK(solver->eliminated);
  RELEASE_STACK(solver->extend);
  RELEASE_STACK(solver->witness);
  RELEASE_STACK(solver->etrail);

  RELEASE_STACK(solver->vectors.stack);
  RELEASE_STACK(solver->delayed);

  RELEASE_STACK(solver->clause.lits);
#if defined(LOGGING) || !defined(NDEBUG)
  RELEASE_STACK(solver->resolvent_lits);
#endif

  RELEASE_STACK(solver->arena);

  RELEASE_STACK(solver->units);
  RELEASE_STACK(solver->frames);
  RELEASE_STACK(solver->sorter);
  RELEASE_STACK(solver->trail);

  RELEASE_STACK(solver->analyzed);
  RELEASE_STACK(solver->levels);
  RELEASE_STACK(solver->minimize);
  RELEASE_STACK(solver->poisoned);
  RELEASE_STACK(solver->promote);
  RELEASE_STACK(solver->removable);
  RELEASE_STACK(solver->xorted[0]);
  RELEASE_STACK(solver->xorted[1]);

  RELEASE_STACK(solver->bump);

  RELEASE_STACK(solver->antecedents[0]);
  RELEASE_STACK(solver->antecedents[1]);
  RELEASE_STACK(solver->gates[0]);
  RELEASE_STACK(solver->gates[1]);
  RELEASE_STACK(solver->resolvents);

#if !defined(NDEBUG) || !defined(NPROOFS)
  RELEASE_STACK(solver->added);
  RELEASE_STACK(solver->removed);
#endif

#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
  RELEASE_STACK(solver->original);
#endif

#ifndef QUIET
  RELEASE_STACK(solver->profiles.stack);
#endif

#ifndef NDEBUG
  kissat_release_checker(solver);
#endif
#if !defined(NDEBUG) && !defined(NMETRICS)
  uint64_t leaked = solver->statistics.allocated_current;
  if (leaked)
    if (!getenv("LEAK"))
      kissat_fatal("internally leaking %" PRIu64 " bytes", leaked);
#endif

  kissat_free(0, solver, sizeof *solver);
}

void kissat_reserve(kissat *solver, int max_var)
{
  kissat_require_initialized(solver);
  kissat_require(0 <= max_var,
                 "negative maximum variable argument '%d'", max_var);
  kissat_require(max_var <= EXTERNAL_MAX_VAR,
                 "invalid maximum variable argument '%d'", max_var);
  kissat_increase_size(solver, (unsigned)max_var);
}

int kissat_get_option(kissat *solver, const char *name)
{
  kissat_require_initialized(solver);
  kissat_require(name, "name zero pointer");
#ifndef NOPTIONS
  return kissat_options_get(&solver->options, name);
#else
  (void)solver;
  return kissat_options_get(name);
#endif
}

int kissat_set_option(kissat *solver, const char *name, int new_value)
{
#ifndef NOPTIONS
  kissat_require_initialized(solver);
  kissat_require(name, "name zero pointer");
#ifndef NOPTIONS
  return kissat_options_set(&solver->options, name, new_value);
#else
  return kissat_options_set(name, new_value);
#endif
#else
  (void)solver, (void)new_value;
  return kissat_options_get(name);
#endif
}

void kissat_set_decision_limit(kissat *solver, unsigned limit)
{
  kissat_require_initialized(solver);
  limits *limits = &solver->limits;
  limited *limited = &solver->limited;
  statistics *statistics = &solver->statistics;
  limited->decisions = true;
  assert(UINT64_MAX - limit >= statistics->decisions);
  limits->decisions = statistics->decisions + limit;
  LOG("set decision limit to %" PRIu64 " after %u decisions",
      limits->decisions, limit);
}

void kissat_set_conflict_limit(kissat *solver, unsigned limit)
{
  kissat_require_initialized(solver);
  limits *limits = &solver->limits;
  limited *limited = &solver->limited;
  statistics *statistics = &solver->statistics;
  limited->conflicts = true;
  assert(UINT64_MAX - limit >= statistics->conflicts);
  limits->conflicts = statistics->conflicts + limit;
  LOG("set conflict limit to %" PRIu64 " after %u conflicts",
      limits->conflicts, limit);
}

void kissat_print_statistics(kissat *solver)
{
#ifndef QUIET
  kissat_require_initialized(solver);
  const int verbosity = kissat_verbosity(solver);
  if (verbosity < 0)
    return;
  if (GET_OPTION(profile))
  {
    kissat_section(solver, "profiling");
    kissat_profiles_print(solver);
  }
  const bool complete = GET_OPTION(statistics);
  kissat_section(solver, "statistics");
  const bool verbose = (complete || verbosity > 0);
  kissat_statistics_print(solver, verbose);
  if (solver->mab)
  {
    printf("c MAB stats : ");
    for (unsigned i = 0; i < solver->mab_heuristics; i++)
      printf("%d ", solver->mab_select[i]);
    printf("\n");
  }
#ifndef NPROOFS
  if (solver->proof)
  {
    kissat_section(solver, "proof");
    kissat_print_proof_statistics(solver, verbose);
  }
#endif
#ifndef NDEBUG
  if (GET_OPTION(check) > 1)
  {
    kissat_section(solver, "checker");
    kissat_print_checker_statistics(solver, verbose);
  }
#endif
  kissat_section(solver, "resources");
  kissat_print_resources(solver);
#endif
  (void)solver;
}

void kissat_add(kissat *solver, int elit)
{
  kissat_require_initialized(solver);
  kissat_require(!GET(searches), "incremental solving not supported");
#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
  const int checking = kissat_checking(solver);
  const bool logging = kissat_logging(solver);
  const bool proving = kissat_proving(solver);
#endif
  if (elit)
  {
    kissat_require_valid_external_internal(elit);
#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
    if (checking || logging || proving)
      PUSH_STACK(solver->original, elit);
#endif

    unsigned ilit = kissat_import_literal(solver, elit);
    const mark mark = MARK(ilit);
    if (!mark)
    {
      const value value = kissat_fixed(solver, ilit);
      if (value > 0)
      {
        if (!solver->clause.satisfied)
        {
          LOG("adding root level satisfied literal %u(%d)@0=1",
              ilit, elit);
          solver->clause.satisfied = true;
        }
      }
      else if (value < 0)
      {
        LOG("adding root level falsified literal %u(%d)@0=-1",
            ilit, elit);
        if (!solver->clause.shrink)
        {
          solver->clause.shrink = true;
          LOG("thus original clause needs shrinking");
        }
      }
      else
      {
        MARK(ilit) = 1;
        MARK(NOT(ilit)) = -1;
        assert(SIZE_STACK(solver->clause.lits) < UINT_MAX);
        PUSH_STACK(solver->clause.lits, ilit);
      }
    }
    else if (mark < 0)
    {
      assert(mark < 0);
      if (!solver->clause.trivial)
      {
        LOG("adding dual literal %u(%d) and %u(%d)",
            NOT(ilit), -elit, ilit, elit);
        solver->clause.trivial = true;
      }
    }
    else
    {
      assert(mark > 0);
      LOG("adding duplicated literal %u(%d)", ilit, elit);
      if (!solver->clause.shrink)
      {
        solver->clause.shrink = true;
        LOG("thus original clause needs shrinking");
      }
    }
  }
  else
  {
#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
    const size_t offset = solver->offset_of_last_original_clause;
    size_t esize = SIZE_STACK(solver->original) - offset;
    int *elits = BEGIN_STACK(solver->original) + offset;
    assert(esize <= UINT_MAX);
#endif
    ADD_UNCHECKED_EXTERNAL(esize, elits);
    const size_t isize = SIZE_STACK(solver->clause.lits);
    unsigned *ilits = BEGIN_STACK(solver->clause.lits);
    assert(isize < (unsigned)INT_MAX);

    if (solver->inconsistent)
      LOG("inconsistent thus skipping original clause");
    else if (solver->clause.satisfied)
      LOG("skipping satisfied original clause");
    else if (solver->clause.trivial)
      LOG("skipping trivial original clause");
    else
    {
      kissat_activate_literals(solver, isize, ilits);

      if (!isize)
      {
        if (solver->clause.shrink)
          LOG("all original clause literals root level falsified");
        else
          LOG("found empty original clause");

        if (!solver->inconsistent)
        {
          LOG("thus solver becomes inconsistent");
          solver->inconsistent = true;
          CHECK_AND_ADD_EMPTY();
          ADD_EMPTY_TO_PROOF();
        }
      }
      else if (isize == 1)
      {
        unsigned unit = TOP_STACK(solver->clause.lits);

        if (solver->clause.shrink)
          LOGUNARY(unit, "original clause shrinks to");
        else
          LOGUNARY(unit, "found original");

        kissat_assign_unit(solver, unit);

        if (!solver->level)
        {
          clause *conflict = kissat_search_propagate(solver);
          if (conflict)
          {
            LOG("propagation of root level unit failed");
            solver->inconsistent = true;
            CHECK_AND_ADD_EMPTY();
            ADD_EMPTY_TO_PROOF();
          }
        }
      }
      else
      {
        reference res = kissat_new_original_clause(solver);

        const unsigned a = ilits[0];
        const unsigned b = ilits[1];

        const value u = VALUE(a);
        const value v = VALUE(b);

        const unsigned k = u ? LEVEL(a) : UINT_MAX;
        const unsigned l = v ? LEVEL(b) : UINT_MAX;

        bool assign = false;

        if (!u && v < 0)
        {
          LOG("original clause immediately forcing");
          assign = true;
        }
        else if (u < 0 && k == l)
        {
          LOG("both watches falsified at level @%u", k);
          assert(v < 0);
          assert(k > 0);
          kissat_backtrack(solver, k - 1);
        }
        else if (u < 0)
        {
          LOG("watches falsified at levels @%u and @%u", k, l);
          assert(v < 0);
          assert(k > l);
          assert(l > 0);
          assign = true;
        }
        else if (u > 0 && v < 0)
        {
          LOG("first watch satisfied at level @%u "
              "second falsified at level @%u",
              k, l);
          assert(k <= l);
        }
        else if (!u && v > 0)
        {
          LOG("first watch unassigned "
              "second falsified at level @%u",
              l);
          assign = true;
        }
        else
        {
          assert(!u);
          assert(!v);
        }

        if (assign)
        {
          assert(solver->level > 0);

          if (isize == 2)
          {
            assert(res == INVALID_REF);
            kissat_assign_binary(solver, false, a, b);
          }
          else
          {
            assert(res != INVALID_REF);
            clause *c = kissat_dereference_clause(solver, res);
            kissat_assign_reference(solver, a, res, c);
          }
        }
      }
    }

#if !defined(NDEBUG) || !defined(NPROOFS)
    if (solver->clause.satisfied || solver->clause.trivial)
    {
#ifndef NDEBUG
      if (checking > 1)
        kissat_remove_checker_external(solver, esize, elits);
#endif
#ifndef NPROOFS
      if (proving)
        kissat_delete_external_from_proof(solver, esize, elits);
#endif
    }
    else if (solver->clause.shrink)
    {
#ifndef NDEBUG
      if (checking > 1)
      {
        kissat_check_and_add_internal(solver, isize, ilits);
        kissat_remove_checker_external(solver, esize, elits);
      }
#endif
#ifndef NPROOFS
      if (proving)
      {
        kissat_add_lits_to_proof(solver, isize, ilits);
        kissat_delete_external_from_proof(solver, esize, elits);
      }
#endif
    }
#endif

#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
    if (checking)
    {
      LOGINTS(esize, elits, "saved original");
      PUSH_STACK(solver->original, 0);
      solver->offset_of_last_original_clause =
          SIZE_STACK(solver->original);
    }
    else if (logging || proving)
    {
      LOGINTS(esize, elits, "reset original");
      CLEAR_STACK(solver->original);
      solver->offset_of_last_original_clause = 0;
    }
#endif
    for (all_stack(unsigned, lit, solver->clause.lits))
      MARK(lit) = MARK(NOT(lit)) = 0;

    CLEAR_STACK(solver->clause.lits);

    solver->clause.satisfied = false;
    solver->clause.trivial = false;
    solver->clause.shrink = 0;
  }
}

int kissat_solve(kissat *solver)
{
  kissat_require_initialized(solver);
  kissat_require(EMPTY_STACK(solver->clause.lits),
                 "incomplete clause (terminating zero not added)");
  kissat_require(!GET(searches), "incremental solving not supported");
  return kissat_search(solver);
}

void kissat_terminate(kissat *solver)
{
  kissat_require_initialized(solver);
  solver->terminate = ~(unsigned)0;
  assert(solver->terminate);
}

int kissat_value(kissat *solver, int elit)
{
  kissat_require_initialized(solver);
  kissat_require_valid_external_internal(elit);
  const unsigned eidx = ABS(elit);
  if (eidx >= SIZE_STACK(solver->import))
    return 0;
  const import *import = &PEEK_STACK(solver->import, eidx);
  if (!import->imported)
    return 0;
  value tmp;
  if (import->eliminated)
  {
    if (!solver->extended && !EMPTY_STACK(solver->extend))
      kissat_extend(solver);
    const unsigned eliminated = import->lit;
    tmp = PEEK_STACK(solver->eliminated, eliminated);
  }
  else
  {
    const unsigned ilit = import->lit;
    tmp = VALUE(ilit);
  }
  if (!tmp)
    return 0;
  if (elit < 0)
    tmp = -tmp;
  return tmp < 0 ? -elit : elit;
}

void setPolarity(kissat *solver, int elit, int p)
{
  unsigned ilit = kissat_import_literal(solver, elit);
  unsigned idx = IDX(ilit);
  phase *phases = solver->phases;
  phases[idx].saved = p;
}

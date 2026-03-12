#include "cadical.hpp"

using namespace CaDiCaL;

extern "C" {
void *cadical_solver_new()
{
	return new Solver();
}

void cadical_solver_free(void *s)
{
	Solver *slv = (Solver *)s;
	delete slv;
}

void cadical_solver_add_clause(void *s, int *clause, int len)
{
	Solver *slv = (Solver *)s;
	for (int i = 0; i < len; ++i) {
		slv->add(clause[i]);
	}
	slv->add(0);
}

int cadical_solver_solve(void *s, int *assumps, int len)
{
	Solver *slv = (Solver *)s;
	for (int i = 0; i < len; ++i)
		slv->assume(assumps[i]);
	return slv->solve();
}

int cadical_solver_model_value(void *s, int lit)
{
	Solver *slv = (Solver *)s;
	return slv->val(lit);
}

bool cadical_solver_conflict_has(void *s, int lit)
{
	Solver *slv = (Solver *)s;
	return slv->failed(lit);
}

void cadical_solver_constrain(void *s, int *constrain, int len)
{
	Solver *slv = (Solver *)s;
	for (int i = 0; i < len; ++i) {
		slv->constrain(constrain[i]);
	}
	slv->constrain(0);
}

int cadical_solver_simplify(void *s)
{
	Solver *slv = (Solver *)s;
	return slv->simplify();
}

int cadical_solver_fixed(void *s, int lit)
{
	Solver *slv = (Solver *)s;
	return slv->fixed(lit);
}

void cadical_solver_freeze(void *s, int lit)
{
	Solver *slv = (Solver *)s;
	slv->freeze(lit);
}

void cadical_terminate(void *s)
{
	Solver *slv = (Solver *)s;
	slv->terminate();
}

struct ClauseIter : ClauseIterator {
	bool clause(const std::vector<int> &c)
	{
		std::vector<int> *cls = new std::vector<int>;
		for (auto &lit : c)
			cls->push_back(lit);
		clauses->push_back(cls->data());
		clauses->push_back((void *)cls->size());
		return true;
	}

	std::vector<void *> *clauses;
};

void *cadical_solver_clauses(void *s, int *len)
{
	ClauseIter clause_iter;
	Solver *slv = (Solver *)s;
	clause_iter.clauses = new std::vector<void *>();
	slv->traverse_clauses(clause_iter);
	*len = clause_iter.clauses->size();
	return clause_iter.clauses->data();
}

void cadical_set_polarity(void *s, int lit)
{
	Solver *slv = (Solver *)s;
	slv->phase(lit);
}

void cadical_unset_polarity(void *s, int lit)
{
	Solver *slv = (Solver *)s;
	slv->unphase(lit);
}

void cadical_set_seed(void *s, int seed)
{
	Solver *slv = (Solver *)s;
	slv->set("seed", seed);
}
}

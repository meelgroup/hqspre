#include "formula.hpp"

namespace hqspre {

Literal Formula::addAndGate(Literal input1, Literal input2)
{
    const Variable output_var = addEVar();
    prefix->moveToRMB(output_var);

    std::vector<Literal> clause(2);

    // input1, ~output
    clause[0] = input1;
    clause[1] = var2lit(output_var, true);
    unsigned int c_nr = addClause(clause);
    clause_gate[c_nr] = true;

    // input2, ~output
    clause[0] = input2;
    c_nr = addClause(clause);
    clause_gate[c_nr] = true;

    // ~input1, ~input2, output
    clause[0] = negate(input1);
    clause[1] = negate(input2);
    clause.push_back( var2lit(output_var, false) );
    c_nr = addClause(clause);
    clause_gate[c_nr] = true;

    ++gate_input[lit2var(input1)];
    ++gate_input[lit2var(input2)];
    gate_output[output_var] = true;

    return var2lit(output_var, false);
}


Literal Formula::addNandGate(Literal input1, Literal input2)
{
    return negate(addAndGate(input1, input2));
}


Literal Formula::addOrGate(Literal input1, Literal input2)
{
    return negate(addAndGate(negate(input1), negate(input2)));
}


Literal Formula::addNorGate(Literal input1, Literal input2)
{
    return addAndGate(negate(input1), negate(input2));
}


Literal Formula::addXorGate(Literal input1, Literal input2)
{
    const Variable output_var = addEVar();
    prefix->moveToRMB(output_var);

    std::vector<Literal> clause(3, 0);

    // ~input1, input2, output
    clause[0] = negate(input1);
    clause[1] = input2;
    clause[2] = var2lit(output_var, false);
    unsigned int c_nr = addClause(clause);
    clause_gate[c_nr] = true;

    // input1, ~input2, output
    clause[0] = input1;
    clause[1] = negate(input2);
    // output did not change
    c_nr = addClause(clause);
    clause_gate[c_nr] = true;

    // input1, input2, ~output
    clause[0] = input1;
    clause[1] = input2;
    clause[2] = var2lit(output_var, true);
    c_nr = addClause(clause);
    clause_gate[c_nr] = true;

    // ~input1, ~input2, ~output
    clause[0] = negate(input1);
    clause[1] = negate(input2);
    // output did not change
    c_nr = addClause(clause);
    clause_gate[c_nr] = true;

    ++gate_input[lit2var(input1)];
    ++gate_input[lit2var(input2)];
    gate_output[output_var] = true;

    return var2lit(output_var, false);
}

} // end namespace hqspre

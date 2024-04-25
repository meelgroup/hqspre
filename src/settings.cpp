#include <ostream>
#include "settings.hpp"

namespace hqspre {

static inline const char* format(bool v)
{
    return (v ? "yes": "no");
}

std::ostream& operator<<(std::ostream& stream, const Settings& s)
{
  stream << "[CONFIG] Maximal number of preprocessor loops: " << s.max_loops << std::endl
         << "[CONFIG] Apply universal reduction: " << format(s.univ_reduction) << std::endl
         << "[CONFIG] Apply blocked clause elimination: " << s.bce << std::endl
         << "[CONFIG] Add hidden literals: " << s.hidden << std::endl
         << "[CONFIG] Add covered literals: " << format(s.covered) << std::endl
         << "[CONFIG] Apply blocked literal elimination: " << format(s.ble) << std::endl
         << "[CONFIG] Apply blocked literal addition: " << format(s.bla) << std::endl
         << "[CONFIG] Apply blocked implication addition: " << format(s.bia) << std::endl
         << "[CONFIG] Maximimal hidden/covered clause size: " << s.max_clause_size << std::endl
         << "[CONFIG] Apply hidden subsumption elimination: " << format(s.hse) << std::endl
         << "[CONFIG] Detect hidden equivalences and constants: " << s.hec << std::endl
         << "[CONFIG] Detect implication chains: " << format(s.impl_chains) << std::endl
         << "[CONFIG] Detect contradictions: " << format(s.contradictions) << std::endl
         << "[CONFIG] Apply gate substitutions: " << format(s.substitution) << " with maximal costs " << s.max_substitution_cost << std::endl
         << "[CONFIG] Apply gate rewriting: " << format(s.rewrite) << std::endl
         << "[CONFIG] Apply self subsumption: " << format(s.self_subsumption) << std::endl
         << "[CONFIG] Apply subsumption: " << format(s.subsumption) << std::endl
         << "[CONFIG] Apply resolution: " << format(s.resolution) << " with maximal costs " << s.max_resolution_cost << std::endl
         << "[CONFIG] Apply SAT-based constant checks: " << format(s.sat_const) << std::endl
         << "[CONFIG] Apply SAT-based implication checks: " << format(s.sat_impl) << std::endl
         << "[CONFIG] Apply SAT-based incomplete decision methods: " << format(s.sat_incomplete) << std::endl
         << "[CONFIG] Apply universal expansion: " << s.univ_expand << std::endl
         << "[CONFIG] Try to preserve gates: " << s.preserve_gates << std::endl
         << "[CONFIG] Verbosity: " << s.verbosity << std::endl
         << "[CONFIG] Force DQBF prefix: " << s.force_dqbf << std::endl
         << "[CONFIG] Apply consistency checks: " << s.verbosity << std::endl;
    return stream;
}

} // end namespace hqspre

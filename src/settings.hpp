#ifndef HQSPRE_SETTINGS_HPP_
#define HQSPRE_SETTINGS_HPP_

/**
 * \file settings.hpp
 * \brief Settings for DQBF preprocessor.
 * \author Sven Reimer
 * \date 2016
 */

namespace hqspre {

/**
 * \brief Represents the settings of the preprocessor
 */
class Settings
{
public:
    //@{
    /**\name Construction, destruction, and assigment
     */

    /**
     * \brief Constructs an default settings.
     */
    Settings()                                = default;

    /**
     * \brief Copy constructor
     */
    Settings(const Settings&)                 = default;


    /**
     * \brief Move constructor
     */
    Settings(Settings&&)                      = default;

    /**
     * \brief Frees the memory occupied by the settings.
     */
    ~Settings() noexcept                      = default;

    /**
     * \brief Assignment of settings
     */
    Settings& operator=(const Settings&)      = default;

    /**
     * \brief Move assignment
     */
    Settings& operator=(Settings&&)           = default;
    //@}


    //@{
    /**
     * \name Variables for storing the current preprocessor configuration
     */
    unsigned int max_loops = 1000; ///< Maximal number of preprocessing iterations
    bool univ_reduction = true;    ///< Use universal reduction
    unsigned int bce = 2;          ///< Use blocked clause elimination (BCE)
    unsigned int hidden = 0;       ///< Improve BCE by hidden literal addition (HLA)
    bool covered = true;           ///< Improve BCE by covered literal addition (CLA)
    bool ble = true;               ///< Use blocked literal elimination (BLE) for universal literals
    bool bla = true;               ///< Use blocked literal addition (BLA) for universal literals
    bool bia = false;              ///< Add blocked implications
    unsigned int max_clause_size = 256; ///< Maximal size for an extended clause by hidden or covered extension
    bool hse = true;               ///< Use hidden subsumption elimination (HSE)
    bool hec = false;              ///< Find hidden equivalences and contradiction
    bool impl_chains = true;       ///< Eliminate implication chains
    bool contradictions = true;    ///< Detect contradicting implication chains
    bool substitution = true;      ///< Eliminate Tseitin variables by substitution
    int max_substitution_cost = 100; ///< Maximal increase of the number of literals in the formula by substitution of gates
    unsigned int max_substitution_loops = 2; ///< Maximal number of substitution iterations
    bool rewrite = true;           ///< Replace Tseitin variables by double Plaisted encoding
    bool self_subsumption = true;  ///< Use self-subsuming resolution
    bool subsumption = true;       ///< Use subsumption checks
    bool resolution = true;        ///< Eliminate variables using resolution
    int max_resolution_cost = 0;   ///< Maximal increase of the number of literals in the formula by resolution
    bool sat_const = true;         ///< Use constant detection with SAT
    bool sat_impl = false;         ///< Find implications using SAT
    bool sat_incomplete = true;    ///< Use incomplete SAT-based checks to determine (un)satisfiability of the (D)QBF
    unsigned int univ_expand = 1;  ///< Apply universal expansion if reasonable
    unsigned int max_expansion_size = 0; ///< Maximal expansion size. This value is set and used during universal expansion
    bool preserve_gates = false;   ///< Apply techniques like BCE only to clauses which do not encode gates
    unsigned int verbosity = 0;    ///< Amount of information to print on the screen
    bool force_dqbf = false;       ///< Always use a DQBF prefix instead of switching to QBF when possible
    bool do_consistency_check = true; ///< Check consistence of database after each prepro-function
    //@}
};

std::ostream& operator<<(std::ostream& stream, const Settings& s);

} // end namespace hqspre

#endif

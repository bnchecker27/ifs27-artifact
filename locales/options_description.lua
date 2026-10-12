local locales = {
    en = {
        help = [[Show help information]],
        model = [[Model file to be checked]],
        property = [[Property to be checked]],
        num_samples = [[Number of samples to be used for model checking]],
        probability_tolerance = [[Tolerance for checking if probabilities sum to 1.0]],
        seed = [[Random seed for the sampling-based solvers]],
        solvers = [[Comma list of solvers to use (replaces the default set)]],
        disable_solvers = [[Comma list of solvers to remove from the set]],
        enable_solvers = [[Comma list of solvers to add to the set]],
        features = [[Comma list of optional features: marginal, chart, numval, arith]],
    },
}
return locales
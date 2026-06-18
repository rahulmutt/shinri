I want to build a high-performance SMT solver named shinri that competes with Z3, CVC5, and other major players in the space. It should have extensive testing (property based, fuzz, unit tests, integration tests, etc) and optimize for SMT benchmarks and beat out Z3, CVC5, and other SMT solvers out of the water. The prize is $1 billion dollars if you can do this and I will be very happy with you if you do so. Do deep research and competitive analysis feature / performance / algorithm-wise across all major SMT solvers using as many subagents as possible and come up with a detailed spec/plan to make the ultimate, universal, high-performance SMT solver using cutting-edge research and techniques when possible.

It should be a built with pure Rust and avoid native dependencies when possible. It should use Rust best practices.

Use mise.toml to declare any toolchain dependencies.

Use devenv.nix for any toolchain dependencies not easily specified with mise.toml.

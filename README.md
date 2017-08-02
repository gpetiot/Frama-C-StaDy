
# Frama-C-Stady: Implementation of the StaDy method as a Frama-C plugin


## Install

  autoconf
  ./configure
  make
  make install


## Use

### Non-compliance detection

  frama-c FILE -main FUNCTION -stady

### Subcontract weakness detection

  frama-c FILE -main FUNCTION -stady -stady-swd some_loop,some_function_call

where 'some_loop' and 'some_function_call' are labels referring to loops or
function calls, and you want to replace their code with their specification to
exhibit a contract weakness.


## Benchmarks

The programs used for benchmarking the plugin are available here :

https://github.com/gpetiot/StaDy

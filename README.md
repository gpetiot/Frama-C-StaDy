
# StaDy plugin for Frama-C

This is the repository for the [StaDy plugin](http://gpetiot.github.io/stady.html) for [Frama-C](http://www.frama-c.com/).
StaDy instruments C programs so that proof failures (see the [WP plugin](http://www.frama-c.com/wp.html)) can be diagnosed thanks to automatic test generation (see the [PathCrawler plugin](http://www.frama-c.com/pathcrawler.html)).

Here are the corresponding versions of Frama-C and PathCrawler for each version of StaDy:

| Frama-C        |  StaDy   | PathCrawler (commit ID)                  |
| -------------- | -------- | ---------------------------------------- |
| v14 Silicon    |  v0.2.3  | bbb76c32b22e2eb4f5777196ade9e2eba2c2ad66 |
| v15 Phosphorus |  (soon)  | (soon)                                   |
| v16 Sulfur     |  (soon)  | (soon)                                   |

[Here](https://github.com/gpetiot/StaDy) are the programs used for benchmarking StaDy.


## Building

    autoconf
    ./configure
    make
    make install


## Using StaDy

### Non-compliance detection

    frama-c FILE -main FUNCTION -stady

### Subcontract weakness detection

    frama-c FILE -main FUNCTION -stady -stady-swd some_loop,some_function_call

where 'some_loop' and 'some_function_call' are labels referring to loops or
function calls, and you want to replace their code with their specification to
exhibit a contract weakness.

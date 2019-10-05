
# StaDy plugin for Frama-C

This is the repository for the StaDy plugin for [Frama-C](http://www.frama-c.com/).
StaDy instruments C programs so that proof failures (see the [WP plugin](http://www.frama-c.com/wp.html)) can be diagnosed thanks to automatic test generation (see the [PathCrawler plugin](http://www.frama-c.com/pathcrawler.html)).

Here are the corresponding versions of Frama-C and PathCrawler for each version of StaDy:

| Frama-C        |  StaDy   | PathCrawler (commit ID)                  |
| -------------- | -------- | ---------------------------------------- |
| v14 Silicon    |  v0.2.3  | bbb76c32b22e2eb4f5777196ade9e2eba2c2ad66 |
| v15 Phosphorus |  v0.3.0  | 3be1d9f39982f4ce05c243096020025b5c1d0aec |
| v16 Sulfur     |  v0.4.3  | 62dd256d2a4225a7507287019ae5b11ca9d02075 |
| v19 Potassium  |  v0.5.x  | **this release has not been tested yet** |

[Here](https://github.com/gpetiot/StaDy) are the programs used for benchmarking StaDy.


## Building

    autoconf
    ./configure
    make
    make install


## Using StaDy

The two main features of StaDy are the non-compliance detection (NCD) and the
subcontract weakness detection (SWD).
See the [documentation](doc/README.md) for more details.

### Non-compliance detection

StaDy tries to exhibit a test case whose execution provokes an annotation violation. Non-compliance detection is the default mode of StaDy. One can detect non-compliances between the code and its specification in file F, starting with function M, using the command:

    frama-c F -main M -stady

In the user interface of Frama-C, an annotation violation is pictured with a red bullet.

### Subcontract weakness detection

StaDy tries to exhibit a test case whose execution does not provoke an annotation violation but that is not proved by deductive verification because of a too weak subcontract (loop invariant or called function contract). The subcontract weakness detection in file F starting with function M is done with:

    frama-c F -main M -stady -stady-swd some_loop,some_function_call

where 'some_loop' and 'some_function_call' are labels referring to loops or
function calls, and you want to replace their code with their specification to
exhibit a contract weakness.
For now, there is no strategy or heuristic implemented in StaDy to automatically submit a set of subcontract identifiers.

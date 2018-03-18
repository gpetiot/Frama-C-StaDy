# Example: Non-compliance detection

Let us consider a small example of an array access:

      

	/*@ requires \valid(buffer+(0..size-1)); */
	int f(int * buffer, int size , int ind) {
          return buffer[ind];
	}
      

    

The function f takes a buffer, its size, and an index. The precondition on the first line states that we can read and write in buffer[0], ..., buffer[size-1].

First, we apply the RTE plug-in of Frama-C. RTE adds an ACSL annotation just before the array access:

      

	/*@ assert rte: mem_access: \valid_read(buffer+ind); */
      

    

meaning that buffer has to be large enough so that buffer[ind] can be read. StaDy is then applied. The full command with the call to RTE is:

      frama-c buffer.c -main f -rte -then -stady -stady-stop-when-assert-violated
    

The option -stady-stop-when-assert-violated stops the test generation as soon as an annotation violation is detected. The assertion added by RTE is reported as non-compliant with the code, here is the output of StaDy:

      [stady] all-paths: true
      [stady] 2 test cases
      [stady] Non-Compliance of assert rte: mem_access: \valid_read(buffer+ind);
      LOCATION: buffer.c:4
      TEST DRIVER: testcases___sd_instru_buffer_f/f/testdrivers/TC_1.c
      ind = -214739
      size = 0
    

This means that for any buffer of size 0, trying to read the buffer at size 0, will lead to a runtime error. One can precise the precondition of f to get more meaningful results, we add the following preconditions (highlighted in yellow):

      

	/*@ requires \valid(buffer+(0..size-1));
	    requires 0 <= ind;
	    requires 0 < size;
	*/
	int f(int * buffer, int size , int ind) {
          return buffer[ind];
	}
      

    

Applying StaDy again still exhibits a counterexample:

      [stady] all-paths: true
      [stady] 4 test cases
      [stady] Non-Compliance of assert rte: mem_access: \valid_read(buffer+ind);
      LOCATION: buffer.c:7
      TEST DRIVER: testcases___sd_instru_buffer_f/f/testdrivers/TC_1.c
      buffer[0] = -214739
      ind = 1073652710
      size = 1
    

This means that we cannot access buffer[1073652710] for a buffer of size 1. We finally correct the precondition (highlighted in yellow):

      

	/*@ requires \valid(buffer+(0..size-1));
	    requires 0 <= ind < size;
	*/
	int f(int * buffer, int size , int ind) {
          return buffer[ind];
	}
      

    

This time, there is no error, so we won't stop at the first annotation violation and we will try each size of buffer (as each size follows its own program path). Thus, we add a timeout to limit the exploration:

      frama-c buffer.c -main f -rte -then -stady -stady-stop-when-assert-violated -stady-timeout 7
    

The option -stady-timeout limits the time allocated to test generation, here it cannot take more than 7 seconds. And StaDy does not report any annotation violation:

      [stady] all-paths: true
      [stady] 1177 test cases

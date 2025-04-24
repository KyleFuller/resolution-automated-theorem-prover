
This is a resolution-based tautology checker for the propositional calculus.  The code includes correctness proofs for most of the algorithms as well as tests (both handwritten and randomly generated en masse).  If one has python3 installed for use as a command, one can run this as follows:
```
python3 atp.py [-t] [-f <file with formula to check>]
```
The flag -t specifies the tests to be run, if included.

I plan to possibly prove the remainder of the code correct at some point and then extend the functionality to include the semidecision of first order logic tautologies.
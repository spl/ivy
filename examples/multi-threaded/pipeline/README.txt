A simple parallel, pipeline-processing example using SharC (sharing checker) to
ensure that the sharing rules are observed by the pipeline threads. This is the
example used in the SharC tutorial at http://ivy.cs.berkeley.edu

To compile, type make. This will build the test (pipeline_test) and
the original (non-SharCified) version (pipeline_test_orig). The programs
process inFile.txt to outFile.txt, but produce no messages.

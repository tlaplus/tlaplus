If this directory contains a model and a spec in the built .jar file, TLC 
will check this model unless a model is given on the command line.

This feature is used in the cloud TLC implementation to have a single
unit of deployment (no stale files) and no OS specific path chores.
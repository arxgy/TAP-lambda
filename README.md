# TAP (Privileged)
> This document is provided by Ganxiang Yang @ Apr 20, 2023.
# Intro
This model provides an extended Trusted Abstract Platform (TAP) model with the newly proposed **Privileged Enclave** primitive. **Privileged Enclave** is an efficient extension designed for data sharing and introspection within/onto enclaves.

In this project. the Secure Measurement, Integrity, and Confidentiality (which are decompositions of SRE property) are proved to be maintained in the extended model.
# Setup
Install Boogie 2.16.4.0 on your platform (dotnet is recommended), and export `boogie` to your environment variables.

TODO.
(detailed install steps)

# Run
    $ cd AbstractPlatform
    $ make clean && make all
# Debugg / Develop / Detailed Info
To get elaborated messages about the model, do these things:
1. Substitute the `LOWER/UPPERLEVELOPT` flag with `LOWER/UPPERLEVELOPT_DBG`.
2. Do: 
    ```
    cd AbstractPlatform   
    mkdir dotfiles
    make clean && make <whatever-you-like> && make cut
    ```
    The `LOWER/UPPERLEVELOPT_DBG` flag and `cut` object in Makefile helps you to generate numerous valuable messages, including intermediate code, backend Z3 SMTs, counterexamples, execution times, to mention a few.

# Directory Structure

The are three top-level directories:
* AbstractPlatform (The extened TAP)
* Code (Code Implementation on Penglai-TVM)

<!-- # Setup

First, you will need to install [boogie](https://github.com/boogie-org/boogie). You'll also need to set the BOOGIE environment variable to point to the boogie executable on your system. For example, I set it as follows:

    $ export BOOGIE="mono ~/research/verification/boogie/Binaries/Boogie.exe"

# Abstract Trusted Platform

The trusted abstract platform (TAP) is in AbstractPlatform.

## Running The TAP Proofs

    $ cd AbstractPlatform
    $ make

Don't forget to set $BOOGIE

# Refinement Proofs

The code is in SanctumRefinementProof.bpl and SGXRefinementProof.bpl.

## Running the Refinement Proofs.
    
Just run make!

# Sanctum Model

Sanctum contains all of the Sanctum model.

* Sanctum/Common defines common, types, constants and functions.
* Sanctum/Host/OS.bpl contains functions that would be implemented in the operating system.
* Sanctum/MMU contains the MMU. See below for details.
* Sanctum/Sanctum contains the Sanctum model and non-interference proofs.

## Executing the Proofs

To run all proofs for the Sanctum model (including the MMU proof), just run make in Sanctum.

    $ cd Sanctum
    $ make

Running all the proofs may take several minutes. (There are a couple of extra proofs that aren't mentioned in the paper here.)

# SGX Model
    
The SGX model is in SGX.  There is nothing to run here.
 -->

# $\text{TAP}^{\lambda}$
> This document is provided by Anonymous Author @ Apr 29, 2024.
# Intro
This model provides an extended Trusted Abstract Platform (TAP) model with the newly proposed **Privileged Enclave** and **Multi-Layered Privilege** prototype.

In this project. the Secure Measurement, Integrity, and Confidentiality (which are decompositions of SRE property) are proved to be maintained in the extended model.
# Setup
Install Boogie 2.16.0 on your platform (dotnet is recommended), and export `boogie` to your environment variables.


    // Update your apt package.
    wget https://packages.microsoft.com/config/ubuntu/20.04/packages-microsoft-prod.deb -O packages-microsoft-prod.deb
    sudo dpkg -i packages-microsoft-prod.deb
    rm packages-microsoft-prod.deb

    // Install .NET 6.0 & Z3
    sudo apt-get update && \ sudo apt-get install -y dotnet-sdk-6.0 aspnetcore-runtime-6.0 z3
    
    // Install boogie 2.16
    dotnet tool install --global boogie --version 2.16

    // Add Boogie toolchains to your environment variables. (optional)
    export PATH=$PATH:$HOME/.dotnet/tools/

    
# Run
    $ cd AbstractPlatform
    $ make clean && make all
# Debug / Develop / Detailed Info
To get elaborated messages about the model, do these things:
1. Use the make-object with the `_dbg` postfix.
2. Do: 
   
    ```
    cd AbstractPlatform   
    mkdir dotfiles
    make clean && make <whatever-you-like> && make cut
    ```
    The `LOWER/UPPERLEVELOPT_DBG` flag and `cut` object in Makefile helps you to generate numerous valuable messages, including intermediate code, backend Z3 SMTs, counterexamples, execution times, and so forth.

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

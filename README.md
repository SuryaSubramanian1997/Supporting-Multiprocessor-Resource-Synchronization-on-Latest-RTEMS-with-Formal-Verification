# Supporting-Multiprocessor-Resource-Synchronization-on-Latest-RTEMS-with-Formal-Verification

The rest of the document is organized as follows:
1. [Patching RTEMS with new protocols](#patching)
2. [Frama-C installation](#installation)
3. [Formal verification of RTEMS source code](#how-to-use-frama-c)

## Patching RTEMS with new protocols

For this thesis, RTEMS 5.1 is used and the original source code can be found at https://ftp.rtems.org/pub/rtems/releases/5/5.1/sources/rtems-5.1.tar.xz.

After installing the toolchain, the patch can be applied to the rtems kernel

<br />
Before applying the patch, please make sure that you have downloaded the correct version or RTEMS

        patch -p1 < RTEMS_file.patch

<br />

## Frama-C installation

For formal verification we have used Frama-C 25.0 version.

It can be downloaded from https://frama-c.com/fc-versions/manganese.html

Please follow the instructions provided there for installation.

## Formal verification of RTEMS source code

As of now support for only PowerPC architecture is present from Frama-C.

So, please use any board support package that uses PowerPC architecture to perform formal verification.

We have used qoriq_e6500_32 board support package.

Please add the ACSL contracts in the /cpukit directory inside rtems kernel.

The following command should be invoked within the /cpukit drectory.

frama-c-gui       -cpp-command '${home}/RTEMS/build/bin/powerpc-rtems5-gcc -C -E \
      -I./include -I./score/cpu/powerpc/include/ \
      -I../../rtems-build/powerpc-rtems5/c/qoriq_e6500_32/include/ \
      -I${home}/RTEMS/build/lib/gcc/powerpc-rtems5/7.5.0/include \
      -I${home}/RTEMS/build/powerpc-rtems5/include \
      -nostdinc -include hdga_contracts.h' -machdep ppc_32 -cpp-frama-c-compliant -c11       include/rtems/score/hdgaimpl.h
   
      
      
      

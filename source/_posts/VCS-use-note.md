---
title: VCS use note
top: false
cover: false
toc: true
mathjax: true
date: 2019-12-14 14:15:23
password:
summary:
tags: setup
categories: VCS
---


VCS的编译链接过程和一般c/c++的过程类似，只是叫法有些区别。
<!--- more --->
c/c++中，源文件(*.c, *.cpp)经过compile和link两个过程形成最终可执行文件。
VCS中，简单地类比，HDL源文件(*.vhd, *.v, *sv)经过analyze，elaborate，最终生成可执行文件simv。

# 1. Analyzing the Design
VCS根据源HDL文件使用语言不同，提供两个analyze的指令***vhdlan*** 和 ***vlogan***。
最终生成待连接文件，过程和c中的compile类似。如果是systemverilog，需要加上-sverilog选项。
实际上，这个过程更多的是为后续的准备工作。这个过程会生成一个AN.DB的数据包，用于后续编译连接工作。

# 2. Elaborating the Design
VCS的连接过程叫做elaborate，指令比较单一，仅是 vcs [-options] filename. 最终会生成simv可执行文件。
这个过程实际上比一般的连接工作要多一些。VCS本质上用的是C/C++来进行最终编译连接形成simv。那么对于HDL类型输入文件，
VCS就会有一个从HDL到C的翻译过程。换句话说，VCS在elaborate过程做的是:
1. 翻译HDL文件到C文件
2. 将C文件编译形成二进制待连接文件
3. 将二进制文件连接形成可执行文件simv  

所以在VCS的elaborate过程会生成一个csrc文件夹，用以存放上述产生的这些文件。

# 3. Simulating the Design
这个过程仅是运行simv，没什么特别的。

# 4. Build flow
VCS文档中划分了两种建立过程，Two-step flow和Three-step flow。本质上其实是一种，只不过three-step是把two-step的第一步细分而已.
Two step = Compilation(Analyze+Elaborate) + Simulation
Three step = Analyze + Elaborate + Simulation

一般情况下，two-step就可以了。但如果要跨语言和使用外部提供的待连接文件，那就要用three-step。

## 4.1 Two-step flow
### compilation (Analyze + Elaborate)
> % vcs [compile_options] Verilog_files

### Simulation
> % simv [run_options]

## 4.2 Three-step flow
Analysis ___(Always analyze Verilog/Systemverilog before VHDL.)___
> % vlogan [vlogan_options] file1.v file2.v
> % vlogan -sverilog [vlogan_options] file1.sv file2.sv file3.sv
> % vhdlan [vhdlan_options] file3.vhd file4.vhd
> **注: 如果有vhdl文件, 那么要先编译它们, 并且编译顺序是从设计层级的底部向上, 走bottom-up路线.**

Elaboration
> % vcs [elaboration_options] **design_unit**
> The design_unit can be one of the following:
> * module
> Verilog top module name.
> * entity
> VHDL top entity name.
> * entity__archname
> Name of the top entity and architecture to be simulated. By
> default, archname is the most recently analyzed architecture.
> * cfgname
> Name of the top-level event configuration to be simulated.

Simulation
> % simv [run_options]

## 4.3 Default Time Unit and Time Precision
verilog和systemverilog中的默认时间单位是1秒。默认的是时间精度也是1秒。
在vhdl中，没有默认时间这个概念，要用到时间，必须加上时间单位，比如: wait for 10.123123 ns;

# 5. Commonly used options in analyze step
Using 'vhdlan' is similar, here we don't describe it but only vlogan.
- -nc
Suppresses the Synopsys copyright message.

- -q
Suppresses all vlogan messages.
- -f filename
Specifies a file that contains a list of source files.
Note: The maximum line length in the specified file filename
must be less than 1024 characters. VCS truncates the line exceeding
this limit and issues a warning message.

- -full64
Analyzes the design for 64-bit simulation.

- -l filename
Specifies a log file where VCS records the analyzer messages.

- -sverilog
Enables the analysis of SystemVerilog source code.

- -timescale=time_unit/time_precision
This option enables you to specify the timescale for the source
files that do not contain ‘timescale compiler directive and
precede the source files that contain.
Do not include spaces when specifying the arguments to this option.

- -v library_file
Specifies a Verilog library file to search for module definitions.

- +define+macro
Defines a text macro. Test this definition in your Verilog source
code using the ‘ifdef compiler directive.

- +libext+extension+
Specifies that VCS searches only for files with the specified file
name extensions in a library directory. You can specify more than
one extension, separating the extensions with the plus (+)
character. For example, +libext+.v+.V+ specifies searching
files with either the .v or .V extension in a library.

- +incdir+directory
Specifies the directories that contain the files specified with the
‘include compiler directive. You can specify more than one
directory, separating each path name with the “+” character.

- +systemverilogext+ext
Specifies a file name extension for SystemVerilog source files.
  ***If you use a different file name extension for the SystemVerilog part of your source code and you use this option, the –sverilog option will be omitted.***


# 6. Commonly used options in elaboration step
使用文档中建议，在elaborate的过程中，可以先使用调试模式来elaborate以保证正确性，之后再切换到优化模式或者关掉调试模式。一般优化模式在跑测试回归的时候会使用。

The syntax to use ***vcs*** is as follows:
> % vcs [elab_options] [libname.]design_unit

- libname
The library name where you analyzed your top module, entity, or the configuration.
- design_unit
  ***design_unit*** is the same as in 4.2.

## 6.1 Commonly Used Options
- -full64
Enables elaboration and simulation in 64-bit mode.

- -file filename
Specifies a file containing elaboration options.

- -R
Runs the executable file immediately after VCS links it together.

- -j[number_of_processes]
by specifying the number of parallel processes VCS can launch for the native code generation phase of the compilation/elaboration.

## 6.2 Debug Mode Options
***some examples:***
Compiling/Elaborating the Design in the Partial Debug Read Mode
> % vcs -debug_access+r [compile_options] TOP.v

Compiling/Elaborating the Design in the Full Debug Mode
> % vcs -debug_access+all [compile_options] TOP.v

Compiling/Elaborating the Design With the Desired Debug Capability
> % vcs -debug_access<+options> [compile_options] TOP.v

Commonly used options of ***-debug_access[+option]***
* +r
This option enables the read capability for the entire design. This is the minimum debug option to invoke the Verdi interactive mode.
* +w
This option applies write (deposit) capability to the registers and variables for the entire design.
* +f
This option enables the following:
• Read capability on registers, variables, and nets
• Write (deposit) capability on registers and variables
• Force capability on registers, variables, and nets
This option is equivalent to -debug_access+r+w+fn+f
* +drivers
This option enables driver debugging capability.
This option is equivalent to -debug_access+r+drivers.
* +reverse
This option enables the reverse debugging feature.
* +pp
This option enables write capability on registers and variables, callbacks for
the entire design, driver capability, and assertion debug capability.
This option is equivalent to: -debug_access+w+cbk+drivers


# 7. Obtaining Consumption of CPU Resources
Specify -reportstats option at compile time as well as runtime or both depending on your requirement.
> %vcs -reportstats
> %simv -reportstats

When specifying this option at compile time, VCS prints out the following information.

Compilation Performance Summary:
> vcs started at: Mon Jan 01 1:02:03 2005
> Elapsed time: 5 sec
> CPU Time: 3.0 sec
> Virtual memory size: 12 MB
> Resident set size: 113 MB
> Shared memory size: 65 MB
> Private memory size: 63 MB
> Major page faults: 0

Simulation Performance Summary:
> Simulation started at : Mon Jan 01 1:02:03 2005
> Elapsed Time: 1 sec
> CPU Time: 0.1 sec
> Virtual memory size: 150 MB
> Resident set size: 100 MB
> Shared memory size: 20 MB
> Private memory size: 83.7 MB
> Major page faults: 0

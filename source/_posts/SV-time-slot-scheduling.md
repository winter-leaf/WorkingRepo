---
title: SV-time slot scheduling
top: false
cover: false
toc: true
mathjax: true
date: 2021-05-16 11:06:31
password:
summary:
tags: SystemVerilog
categories: SystemVerilog
---


记录一下对systemverilog时间片中区域调度的理解。

<!--- more --->

# 1. systemverilog时间片
SV中时间片称为一个step或slot。Step是SV中的最小时间采样单位。
与step关联的SV特殊关键字是 _#1step_ (只有_#1step_, 没有_#2step_ ...等等)。_#1step_ 等价于一个单位的global time precision。Global time precision又称为simulation time unit，是一个全局变量。其值是所有在仿真过程中遇到的time precision的最小值。
比如仿真中遇到的最小time precision是_1ps_，那么_#1step_ = _1ps_。
SV中的仿真时间会以1个step为单位进行分割。分割出来的每个时间片又会被分为不同的event region。

# 2. 仿真时间分割
仿真时间片从preponed区域开始到postpone区域结束。可以对应理解为begin-end。
对相邻两个时间片内的preponed和postpone区域而言，除仿真时间的不同外，在信号采样和变量更新操作上本质区别，两个区域可以看做相互等价。具体看下图:

![sv_time](sv-time.jpg)


# 3. event region

## 3.1 event region类别
SV中的event region主要为分两个类别，分别作用于两个不同的语言接口 － Systemverilog本身和PLI。
PLI指Programming Language Interface。用于除SV语言外的其他语言，如C/C++，对进行SV中已实例化的数据结构进行访问。已实例化的数据结构通常是编译或层级解析过的对象实例。有的时候会碰到另一个术语VPI(Verification Procedural Interface)。它本身属于PLI的一部分，也是一个C函数库。VPI用于连接C函数和SV函数(类似于DPI)。


## 3.2 各region作用和联系
PLI region的用法类似callback，它并不出现在正常的仿真路径上。一般情况下会被仿真器用于记录信号/变量值来dump波形。这里不对其讨论。其他region的作用看下图:

![time_slot](time-slot.jpg)



# 4. Reference
1. systemverilog-IEEE.std.1800-2017
2. SystemVerilog Event Regions, Race Avoidance & Guidelines. Clifford E. Cummings, Arturo Salz, SNUG2006


---
title: Regarding sampling event in SVA
top: false
cover: false
toc: true
mathjax: true
date: 2021-05-23 17:15:13
password:
summary:
tags: SVA
categories: SystemVerilog
---

做一些SVA里触发机制的小记。

<!--- more --->

# 1. Sampled value functions
除$sampled(expressioin)外，有如下行为采样函数。

~~~verilog
$rose ( expression [, [clocking_event] ] )
$fell ( expression [, [clocking_event] ] )
$stable ( expression [, [clocking_event] ] )
$changed ( expression [ , [ clocking_event ] ] )
$past ( expression1 [, [number_of_ticks ] [, [expression2 ] [, [clocking_event]]] ] )
~~~

以上这些行为采样函数都需要一前一后两个触发点的采样值来判断行为是否成立。
$past中的*expression2*为使能条件。
两个采样触发点分别是:  
1. 当前触发点即函数被调用的触发时间点。
2. 之前采样触发点。
之前采样触发点由可省略参数clocking_event来定义。省略时则默认和当前函数被调用时的触发点一样。

例子:

~~~verilog
always_ff @(posedge clk1) begin
  a <= $rose(b, @(posedge clk2));
end
~~~


$rose(b)在clk1的作用域内被触发，所以后采样触发点为posedge clk1。前采样触发点在函数内部显式给出。那么这里的$rose(b)的前后采样触发点分别为posedge clk2和posedge clk1，即  

> (b=0 @ posedge clk2) and (b=1 @posedge clk1)



# 2. Multiclock assertion
SV支持assertion切换触发点。触发点一般为时钟沿，也可以是别的信号变动等。

~~~verilog
sequence 
  @(ev_1) seq_1 ##1 @(ev_2) seq_2 ##1 @(ev_3) ...
endsequence
~~~

##1在此处是一个sequence在时间上的连接符，表示上一个触发条件下seq\_1的结束到下一个触发条件下seq\_2的开始之间的时段。若没有##1，则前后触发条件在发生时间上的重叠会直接触发seq_2。比如clk1和clk2跨时钟域，两个时钟正好在同一时刻出现了上升沿。


## 2.1 Trigger event scope:
SV定义，在不加括号和没有局部新的触发条件的情况下，触发条件由左到有聚拢生效。
换句话说，就是信号或延时都以左边最近的触发条件作基准，直到碰见新的触发条件或有新的局部触发条件。
举例来说,

~~~verilog
sequence
  @(ev_1) seq_1 ##1 @(ev_2) seq_2 ##1 @(ev_3) ...
endsequence
~~~

触发条件ev\_1会影响到seq\_1 ##1，触发条件ev\_2会影响到seq\_2 ##1, ...
如果seq_1单独局部定义新的触发条件，比如

~~~verilog
sequence seq_1
  @(ev_seq) a ##1 b ##2 c ...;
endsequence
~~~

那么触发条件ev\_1不会影响到seq\_1内部，但还是会影响到seq_1后面的##1.

~~~verilog
@(ev_1) seq_1 ##1  (@(ev_2) seq_2 ##1)  ##2 seq_3 ...
~~~

这里(@(ev\_2) seq\_2 ##1)单独加上括号且有独立的触发条件，ev\_1不会影响到其内部。括号外面的还是在ev_1影响范围内。


# 3. Reference
1. systemverilog-IEEE.std.1800-2017

---
title: 'SVA: ''start'' and ''end'' in property'
top: false
cover: false
toc: true
mathjax: true
date: 2019-11-11
password:
summary:
tags: SVA
categories: SystemVerilog
---

SVA的property起始于先行算子终止于后行算子。
<!--- more --->
这个概念有时会在并行检测的时候用到，比如说有一个property要检测“每个周期，当察看到信号a有向上跳变时，信号b在两个周期后为0 或者 信号c在一个周期后为1”。  

  - 信号b在两个周期后为0
  - 信号c在一个周期后为1
 
这里两个后行算子在逻辑上是并列的，但他们共享一个先行算子，且结束时间上不一样，信号c的检测时间要早于b一个周期。
如果写成下面这样是不行的。
```verilog
property;
  @(posedge clk)
  (
    $rose(a)
    |->
    (##1 c ##1 !b)
  );
endproperty
```
两个后行算子会变成串行。

可以利用 ***or*** 操作符来进行并行检测。
```verilog
property;
  @(posedge clk)
  (
    $rose(a) |->
    ((##1 c) or (##2 !b))
  );
endproperty
```
**((##1 c) or (##2 !b))** 以 **$rose(a)** 作为先行条件，**((##1 c)** 和 **(##2 !b))** 并行执行。
整个property的起点是**$rose(a)**，终点的判定要看情况。
 - 如果 **((##1 c)** 和 **(##2 !b))** 有一个成功，那么以成功的时刻为终点
 - 如果 **((##1 c)** 和 **(##2 !b))** 都没成功，那么以最终失败，即时间更长 **(##2 !b))** 为终点

同理还有 ***and*** 操作符，可以检测同时成立的并行。

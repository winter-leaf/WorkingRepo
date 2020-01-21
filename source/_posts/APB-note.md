---
title: APB note
top: false
cover: false
toc: true
mathjax: true
date: 2020-01-21 03:52:59
password:
summary:
tags: APB
categories: AMBA
---

APB的信息传输总共用两步骤/阶段来完成通信:
<!--- more --->
 * 准备阶段，用于发送指令
 * 访问阶段，用于回应指令

一次信息传输的完成至少需要两个周期，且两步必须要完成。
PSELx是片选信号，但实际上可以看做是一个全局的使能信号，它在信息传输时为1, 其余时刻为0. 换句话说，只有在PSELx=1时，两阶段信息传输才进行。
两步用PENABLE信号来区分，准备阶段时PENABLE=0, 访问阶段时PENABLE=1。
准备阶段只有一个周期。访问阶段可以有多个周期但至少一个周期，以slave发送PREADY=1作为结束，在访问阶段PREADY=0时都可以看做是阶段的延长周期。
其他的PADDR，PWRITE，PWDATA，PRDATA信号就是一般的地址和数据线，相对好理解。

分别看一个不延长和延长的例子,
![nowait](nowait.png)
![haswait](haswait.png)

总结来说，在PSELx=1的情况下，第一个周期为准备阶段，第二到第n个PREADY=1的周期为访问阶段。具体的读/写操作看PADDR，PWRITE，PWDATA，PRDATA。

除此之外，还有PRESETn，PSTRB，PPROT，PSLVERR信号。

* PRESETn: 是低电平触发的系统复位信号，没特别的地方。
* PSTRB: 这个信号有点意思，它只作用于写模式，在读模式下必须为0。这是一个8-bit信号，由于APB的数据总线是32-bit，PSTRB的每一位都对应数据线的一个byte。当前位为1时，表示此为对应的byte是有效的，否则对应的byte看做是无效。
* PPROT: 这是个3-bit信号，不常用，它一般是一个附加信号，根据用户的需求，可以用于指定当前指令的等级或者类型。
PSLVERR: 这个信号不常用，它由slave发送，用于指示当前的信息传输是否出错。PSLVERR只在访问阶段的最后一个周期，即PENABLE=1时，才会被识别，其余时间值并不作要求，但建议为0以降低功耗和潜在错误。

APB文档建议，PADDR，PWRITE信号不要在信息传输结束时马上更新其值，而可以等到下一个传输开始时再更新，以此来节省功耗。



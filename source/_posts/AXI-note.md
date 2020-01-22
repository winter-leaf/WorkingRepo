---
title: AXI note
top: false
cover: false
toc: true
mathjax: true
date: 2020-01-22 04:52:09
password:
summary:
tags: AXI
categories: AMBA
---

AXI与APB，AHB很大的一个区别就是将各信号分组，并将分组信号分为了WRITE ADDR，WRITE DATA，WRITE RESP，READ ADDR，READ DATA五个通道。相应的信号数量也较APB，APB增多不少。
<!--- more --->

# 1. globals signals
* ACLK. 时钟信号，没什么特别的。
* ARESETn. 低电平触发的复位信号，没什么特别的。

# 2. read/wtite channels overview
## 2.1 write channels
与写操作相关的有三个通道，如下图:
![writes](writes.png)

除去前缀名"S_AXI\_"，后面的名字就是信号名。各个通道之间相互独立。以WRITE ADDRESS CHANNEL为例，有的信号从名字上便可以推断出其大致功能与APB，AHB中相应名字的信号功能类似，如AWADDR，AWBUTST，AWSIZE，AWPROT。

## 2.2 write channels
与读操作相关的有两个通道，如下图:
![reads](reads.png)

各通道之间相互独立。读操作没有专门的回应通道，因为读操作本身就是需要回应的，所以可以看到read data channel本身就融合了一系列的回应信号。

# 3. * address channels
write/read address channel信号有很大的相似性，所以这里结合起来说明。
* A\*VALID和A\*READY. 这两个信号是通信时的握手信号，当A\*VALID=1 && A\*READY=1时，握手成功，当前周期所提供的数据及指令会被读入且执行。A\*VALID由master发出，A\*READY由slave发出，发送时机相互独立。
这个简单的握手机制也是AXI和APB，AHB的主要区别之一。APB和AHB中，采用双阶段信息传递的方式来等待slave的反馈，master侧并不提供类似VALID的使有效信号，任何在传输阶段的指令，在有效周期(如不在busy时)，都会被识别。并由slave单侧的READY信号来作为结束。AXI采用的握手机制相当于在master侧和slave侧各执一个待握手信号，在双方同时表示同意时握手完成。
A\*VALID由master随着访问地址发出，指明当前发出地址的有效性。
A\*READY由slave发出，指明当前slave的状态，是否处于可接收状态。

* A*ADDR. 地址信号，没什么特别的。

* A\*BURST，A\*SIZE，A\*LEN. 这三个信号是突发模式相关的信号。与AHB不同的是，AXI不像AHB一样将突发的长度与模式一起编码到HBURST信号里，而是分为两个信号A\*BURST与A\*LEN，A\*BURST负责具体的突发模式，A\*LEN负责具体的突发长度，其beat个数，长度为A\*LEN+1。A\*SIZE和AHB中的HSIZE类似，就是beat所含的字节数。具体参考下图。
![burst_type](burst_type.png)
![burst_size](burst_size.png)
突发模式中有几点需要注意:
1. 一次突发中的地址不能跨越以4KB为倍数的地址。
2. 突发不能提前结束或中断，必须发完。如果有多余数据，可以借助写通道中的WSTRB来盖掉不需要的数据。
3. 回卷模式中，突发长度必须是2,4,6,8,16。

* A\*ID，标示符信号，表示当前周期的信息来源，没什么太特别的地方。
* A\*LOCK. 这个信号用于表明lock模式，但除了其中一个locked access模式外，其他的不是很类似AHB中的HMASTLOCK。这个A\*LOCK更像是一个后门访问或者说类似于简单地址DMA访问的概念信号。AXI3和AXI4中，A\*LOCK有很大区别，AXI3中要求必须对A\*LOCK实现的功能，由于其实现起来的复杂性和较少的实用性，在AXI4中被移除。具体可以看下表。
![AXI3_lock](AXI3_lock.png)
![AXI4_lock](AXI4_lock.png)

Locked access类似于AHB中的HMASTLOCK，起一个互斥锁的作用。
Normal access是正常的读写访问模式。
Exclusive access是类似于后门的一种访问方式，通过设定A\*LOCK=Exclusive access来开辟一个专有的读写访问机会。

* A\*PROT. 类似APB，AHB中的PROT信号。
* A\*CACHE. 这个信号一般是在AXI用于与cache类型的器件桥接时，类似于一个cache控制器和cache间传递信号，指明了cache在miss和hit情况下的update policy，如Write-through No-allocate，Write-through Read-allocate等等。
* A\×QOS. 这个信号是AXI4才引入的扩展信号。用于在指示多个信息传递时的优先级。QOS值越大的优先级越高，越应该先被处理。
* A\*REGION. 这个信号是AXI4才引入的扩展信号。类似于AHB中的decoder。AHB中专门实现了一个decoder来进行高位解码，在AXI4中，在master和slave中内部实现并用A\*REGION信号来指示。
* A\*USER. 这个信号是AXI4才引入的扩展信号。此信号是用户自定义信号，可以在通信时用于添加一些附加信息。但官方文档并没有给出严格的定义，也不推荐使用，可以将此信号看做是保留信号。



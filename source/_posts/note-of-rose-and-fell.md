---
title: note of rose and fell
top: false
cover: false
toc: true
mathjax: true
date: 2019-11-16 11:42:09
password:
summary:
tags: SVA
categories: SystemVerilog
---

\$rose(x) 和 \$fell(x) 作为同步于时钟时间的函数，都需要两个有效的时钟事件来触发。
<!---more--->

值得注意的一点是，当x是多位信号，只有在最低位有 上升/下降 变化时，\$rose(x) 和 \$fell(x) 才会触发。
也就是说当 b'0111 -> b'1111 时，\$rose(x) 是不会触发的。

下面是例子

![rose_fell_LSB](rose_fell_LSB.png)


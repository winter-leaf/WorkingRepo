---
title: MIPI - D-PHY
top: false
cover: false
toc: true
mathjax: true
date: 2020-06-07 14:46:58
password:
summary:
tags: D-PHY
categories: MIPI
---

介绍过了C-PHY的编码，接下来看看D-PHY。
<!--- more --->

# 1. D-PHY物理层长什么样？
先祭出图来
![dphy_arch2](dphy_arch2.png)

上图基本显示了D-PHY的导线个数及连接形况。
D- PHY的连接主要分为两部分:
1. Data lane，包含两根导线，称作dp和dn(或d+，d-)
2. Clock lane，包含两根导线，称作clkp和clkn(或c+，c-)


D-PHY的data lane和clock lane都使用差分信号进行通信，这也是为什么每个lane都有正负两根导线。一个clock lane可以和多个data lane组合，及多个data lane可以同时共享一个clock lane。

D-PHY的使用DDR进行采样，即在时钟的上升沿和下降沿进行采样。在差分的clock lane上就是每次差分信号变化的时刻进行采样。

# 2. D-PHY电平等级
与C-PHY类似，D-PHY的通过不同电平等级分为两种工作模式: High-Speed(HS), Low-Power(LP).
LP模式的电平等级及变化幅度高，所需的transition时间也更长，主要负责低频率开关活动的节电工作。
HS模式的电平等级及变化幅度低，所需的transition时间也更短，主要负责高频率的开关活动的数据传输工作。

dp，dn两线在HS和LP两种模式下所出现的电平情况如下图
![dphy_line_lvl](dphy_line_lvl.png)

# 3. D-PHY编码
D-PHY不像C-PHY那样有复杂的intege-symbol和symbol-wire-state的编码转换步骤。

# 4. D-PHY的操作模式
D-PHY的操作模式，如Control mode，High-Speed mode，Escape mode等会在其他文章里合并讲解








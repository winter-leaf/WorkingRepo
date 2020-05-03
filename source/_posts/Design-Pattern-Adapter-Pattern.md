---
title: Design Pattern - Adapter Pattern
top: false
cover: false
toc: true
mathjax: true
date: 2020-05-03 12:20:14
password:
summary:
tags: Design Pattern
categories: pattern
---

具体记不清设计模式是什么时候看的了。最近看源码时，偶尔会碰到一些应用的例子，又想起了相关的一些东西。有的还有些印象，有的已经模糊了。所以决定再把这些概念从以前的记录里扒出来整理一下。
<!--- more --->
设计模式这个概念一般是对于面向对象编程而言的。本质上并不一定是必须的，但它却能一定程度上更好地构建编码结构，以及后续的维护与拓展。对工程实现来说还是很不错的理念。

另一方面，特别是读库源码时，时常会碰到设计模式的应用场景。如果之前不了解，忽然在代码里出来一个adapter或者decorator，多多少少会感到有些突戊和迷惑。若是了解了，可以帮助更好地阅读。同时，或许会对自己有些启发。

# Aapter Pattern
适配器模式(Aapter Pattern)从概念上讲其实是一种函数调用转换器，更广以来说，是一种接口转换器。顾名思义，适配器就是把不合适、不匹配的两个东西变的相互匹配。举例来说，就像是电源转换插头一样，各个国家有不同的插座形状，转换插头就像一个翻译，把输入侧的插头形状转成输出侧插座认识的插头形状。

输入侧和输出侧相互独立，只有适配器两侧都认识。

直接看一个adapter的例子，
~~~verilog
class MyCharger;
  function new();
    ...
  endfunction
  
  virtual function void doCharge();
  endfunction
endclass

class OutletUSA;
  function new();
  endfunction
  
  function void charge();
    ...
  endfunction
endclass

class OutletGER;
  function new();
  endfunction
  
  function void charge();
    ...
  endfunction
endclass

class OutletAdapter#(type Outlet) extends Mycharger;
  Outlet target_ol;

  function new(Outlet ol);
    this.target_ol = ol;
  endfunction
  
  function void doCharge();
	this.target_ol.charge();
  endfunction
endclass

OutletUSA ol_usa = new();
OutletAdapter#(OutletUSA) ol_adapter = new(ol_usa);
MyCharger my_charger = ol_adapter;
my_charger.doCharge();
~~~

例子具体表现了适配器模式。
在输入侧，MyCharger中所有的函数形式都已定义好，但是具体需要与外界通信的函数，由于行为不确定，被定义为虚函数。
在输出侧，我们有已经定义好的，不同类型的OutletUSA和OutletGER。这些类可能是别人提供的具体库，我们一般不能修改。

适配器类本身就是一个Mycharger的具体实现，它实例化的同时把目标输出侧考虑进去，并匹配输出类的接口函数。

输入和输出两侧相互独立。adapter的父类定义待实现函数形式。

# 小结
适配器模式本质上就是一种子类到父类继承上的多态。父类只定义接口函数的骨架，子类负责具体实现。
什么时候用适配器模式比较好? 在父类要与多个外部类通讯，且外部类接口函数不统一的时候。子类在实现的时候会把外部类的类型考虑进去，并负责具体的接口函数调用。

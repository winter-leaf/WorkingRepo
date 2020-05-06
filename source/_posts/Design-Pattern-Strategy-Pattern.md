---
title: Design Pattern - Strategy Pattern
top: false
cover: false
toc: true
mathjax: true
date: 2020-05-07 01:46:23
password:
summary:
tags: Design Pattern
categories: pattern
---

# Strategy Pattern
<!--- more --->
strategy pattern的目的是为了能够使一个对象在"使用同一函数名，但具体实现不同的函数"之间能随意切换。
换句话说，就是对象只调用事先定义好形式的函数骨架，函数的具体实现可以变化。

例子，
~~~verilog
class Runnable;
  function new();
  endfunction
  
  virtual function void run();
  endfunction
endclass

class GoLeft extends Runnable;
  function new();
  endfunction
  
  function void run();
    // go left
	...
  endfunction
endclass

class GoRight extends Runnable;
  function new();
  endfunction
  
  function void run();
    // go right
	...
  endfunction
endclass

class Car;
  Runnable run_behavior;
  
  function new(Runnable run_behavior);
    this.run_behavior = run_behavior;
  endfunction
  
  function void run();
	this.run_behavior.run()
  endfunction
endclass

GoLeft gl = new();
//GoRight gr = new();
Car car = new(gl);
car.run();
~~~

在可以传递函数指针的编程语言里，比如C，直接在目标函数的形参中使用待调用的函数指针也可以达到同样的效果。

在python中更简单一些，
~~~python
def foo():
  ...
  
def bar():
  ...
  
def run_func(func):
  func()
  
run_func(foo)
run_func(bar)
~~~

# 小结
strategy pattern其实就是多态 + 函数指针传递。
对象内部定义/方法的父类骨架，利用多态把子类的具体实现函数替换到父类骨架里。

什么时候用strategy pattern比较好? 在一个函数/方法有多种算法实现，且每种算法都有可能被使用时，可以考虑用strategy pattern来动态替换目标算法。

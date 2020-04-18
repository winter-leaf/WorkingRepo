---
title: interface class vs virtual class
top: false
cover: false
toc: true
mathjax: true
date: 2020-04-18 20:21:46
password:
summary:
tags:
categories: SystemVerilog
---


# virtual class(abstract class)
SV中的虚类(或者叫抽象类)相对好理解，它像是一个定义雏型的蓝图类。用于定义一个要被子类继承的父类的骨架。
<!--- more --->
虚类有下面几个特点:
 - 虚类必须被继承
 - 虚类不能被实例化
 - 虚类和正常类一样，可以在类中定义各类函数
 - 虚类可以，且只有虚类可以使用纯虚函数。纯虚函数指只给出函数声明而没有定义的函数
 - 虚类中可以定义变量

其实从这里看来，虚类除了(1)不能被实例化，(2)必须被继承，(3)可以使用纯虚函数，这三点外，其他和正常类都一样。

例子

```verilog
virtual class A;
  function new();
    $display("A.new() called");
  endfunction
  
  function void foo();
    $display("A.foo() called");
  endfunction
  
  virtual function void bar();
    $display("A.bar() called");
  endfunction
  
  pure virtual function void wea(int asd);
endclass
    
class B extends A;
  function new();
    $display("B.new() called");
  endfunction
  
  function void wea(int asd);
    $display($sformatf("A.wea() called, asd = %0d", asd));
  endfunction
endclass
    
module tb();
  B b;
  
  initial begin
    b = new();
    b.foo();
    b.bar();
    b.wea(123);
  end
endmodule
```

以上的输出是:
> A.new() called
> B.new() called
> A.foo() called
> A.bar() called
> A.wea() called, asd = 123

简单理解的话，虚类就是一个可使用纯虚函数，且专门用于被继承的扩展类。


# interface class
接口类是IEEE Std 1800-2012中引入的新概念，它的主要作用是实现多继承。
原来在SV是没有多继承这个概念的，一个子类只能继承于一种父类。而子类却可以"实现"多个接口类。

这里说"实现"而不是"继承"，是因为接口类的"继承"只能是接口类，而接口类的"实现"只能是非接口类。

接口类的特点如下:
 - 接口类中只能存在与声明相关的内容，如纯虚函数，constraint, coverage group, typedef, localparam/parameter/specparam等常数值. 不能声明变量.
 - 接口类可以被参数化定义，一般只做类型参数化，其他参数化也可以，但对实现类不可见，没什么用
 - 接口类只能被接口类继承, 且可以多"继承"
 - 实现类必须以虚函数的形式实现接口类中的纯虚函数
 
接口类中的"实现"是一个关键字"implements"，例子如下:
~~~verilog
// blocking_get_if#(type T=int), 这里也可以使用#(int var=123)，
// 但var只对这个类可见，后续的实现类都不可见，没什么太大用
interface class blocking_get_if#(type T=int);
  pure virtual task get(output T t);
  pure virtual task peek(output T t);
endclass

// nonblocking_get_if#(type T=int)
interface class nonblocking_get_if#(type T=int);
  pure virtual function bit try_get(output T t);
  pure virtual function bit can_get();
  pure virtual function bit try_peek(output T t);
  pure virtual function bit can_peek();
endclass

// 接口类的多继承
interface class get_if#(type T) extends blocking_get_if #(T), nonblocking_get_if #(T);

// put_if#(type T=int)
interface class put_if#(type T=int);
  pure virtual task put(input T t);
endclass

// 实现类的多实现
class my_port#(type T=int) implements get_if#(T), put_if#(T);
  //--------------------------------------
  // blocking_get_if interface methods ...
  //--------------------------------------
  virtual task get(output T t);
	...
  endtask
  
  virtual task peek(output T t);
	...
  endtask
  
  //-----------------------------------------
  // nonblocking_get_if interface methods ...
  //-----------------------------------------
  virtual task try_get(output T t);
	...
  endtask
  ...
  ...
  
  //-----------------------------------------
  // put_if interface methods ...
  //-----------------------------------------
  virtual task put(input T t);
    ...
  endtask
  
  //-----------------------------------------
  // other user defined methods ...
  //-----------------------------------------
  function new();
    ...
  endfunction
  
  function void foo();
    ...
  endfunction

endclass
~~~


这里我们可能会问，这个多实现到底有什么用? 乍一看上去，就是用一个implements把几个接口类的内容整合到一个实现类中去，没什么特别的东西。从上面的例子来看差不多是这样。但实现类还有一个特点，那就是implements可以同时extends。

看一个例子,
~~~verilog
virtual class my_class extends base_class implements interface_class;
  ...
  ...
  ...
endclass : my_class
~~~

这里my_class在原有继承base_class的基础上又实现了interface_class，这相当于是把interface_class中定义的内容给"塞进"了my_class里，相当于打了一个补丁进去。继承机制的单一性是无法做到这一点的。

这就有意思了，假如说我们已经有了类A，B，C，D, 且A，B继承于base_AB，C, D继承于base_CD. 现在我们要同时向A和C中补充同一个新功能，由于A和C继承于不同的父类，直接在父类中添加新功能的话，会造成代码在两个父类中的重复。我们没办法找到一个合适的地方来存放这个新功能。但有了接口类，我们可以创建一个补丁接口类来存放新功能，然后利用implements向A和C中打入这个补丁。

这对于有时代码库中的父类缺少所需功能，且没法直接改动父类代码时，有很好的补充作用。

简单理解的话，接口类更像是一个补丁类。

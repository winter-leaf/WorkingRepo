---
title: 关于wait
top: false
cover: false
toc: true
mathjax: true
date: 2021-06-14 14:16:11
password:
summary:
tags: SystemVerilog
categories: SystemVerilog
---

做了几个关于wait()的小实验，记录一下结果。

<!--- more --->

# 1. wait的定义问题
wait(expr)的定义是: 在expr结果为0时等待，直到非零值出现后结束等待。
如果expr是一个变量或者信号，变化比较直观，但当expr为函数时怎么界定其值的变化?

# 2. wait的行为
仿真器会在碰到wait(expr)语句时，自动开辟一个新的后台线程。这个线程会以do-while(expr != 0)的方式轮询expr的值变化。换句话说，wait(expr)至少会马上执行一次，若expr结果为0，则继续轮询直到expr为非零值。

expr作为函数有两种形式:
1. 未定义在class中的函数。如定义在module中的函数或定义在compile unit空间中的函数等。
2. 定义在class中的函数。

函数的变化敏感于输入实参，即实参值变化时，认为函数所在expr变化，wait(expr)会被重新评估，对于形式1和2都一样。

比较特殊的是形式2。此形式下，expr为obj.foo(args)。expr不仅仅只关联到一个函数，而是以obj作为关联目标，obj的任何属性变化都会触发wait重新评估。所以除输入实参外，任何obj的成员变化都会重新评估wait。

值得注意的是, 子类自定义的变量变化不会在多态时反应到父类上，因为父类没有定义子类的自有变量。若子类变动继承于父类的变量，多态时变化则可以反应到父类上。实例如下：

~~~verilog
class A;
  int a;
  int b;
  
  function automatic int foo();
    $display("called @ %0d", $time);
    return 0;
  endfunction
endclass
  
class B extends A;
  int c;
endclass

module tb;
  initial begin
    automatic A ca;
    automatic B cb = new();
    ca = cb; 
    
    fork
      wait(ca.foo());
      
      begin
        #10;
        cb.a = 1;
        #10;
        cb.b = 2;
        #10;
        cb.c = 3;
        #10;
        cb.a = 4;
      end
    join
  end
  
endmodule
~~~  

输出为:
> called @ 0
> called @ 10
> called @ 20
> called @ 40

子类中自定义的c变化并没有触发wait的重新评估。

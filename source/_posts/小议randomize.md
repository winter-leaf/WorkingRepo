---
title: 小议randomize
top: false
cover: false
toc: true
mathjax: true
date: 2020-05-17 20:51:43
password:
summary:
tags: randomization
categories: SystemVerilog
---

运行程序时，经常碰到的一个问题是randomize()出错，并花长时间调试constraint。这里稍稍总结一下碰到的问题。
<!--- more --->

# 1. what is randomize() like?
要看constraint-randomize()可能会产生的问题，要先看一下它的运行过程。
当一个类的randomize()函数时，它会按照下述步骤:
1. 以自上到下的方式，层级地调用各自的pre_randomize()函数.
2. 收集并统计各层级对象的rand variable和constraint.
3. 把简单的关于常数的constraint先解决好，比如 constraint c {a==1;}.
4. 解决在constraint中的不以rand variable作为形参的函数。具体看下面解释。
5. 根据上面的步骤结果，更新constraint中的变量值。
6. 把剩下的变量通过各自的互相关联进行聚类和分组，比如在VCS里称作partition。
7. 选择合适的算法引擎解决6中聚类好的变量。
8. 解决在constraint中的以rand variable作为形参的函数。具体看下面解释。
9. 以自上到下的方式，层级地调用各自的post_randomize()函数.


在SV中，constraint中的不使用rand variable作为形参的函数的内部执行过程不会被constraint solver观察到，只会当做普通函数执行。也就是说即使函数执行体中用到了rand variable，函数执行体本身也不会参与到随机约束的过程里，所有函数执行体中出现的rand variable都会使用randomize之前的值执行函数体。函数只有返回值对constraint solver可见。
当函数使用rand variable作为形参时，这些rand形参会与其他的rand variable一样进行随机化。即constraint solver过程会先把这些变量值解决掉，然后再执行函数。
也就是说同样都是函数，但执行时间不一样。比如下面的例子。
~~~
rand int a;
rand int b;

function int bar();
  return b+1;
endfunction

function int foo(int a);
  return a;
endfunction

constraint c {
   foo(a);
   bar();
}
~~~

例子中bar没有rand形参，会在a和b被随机化之前被执行，由于b的默认值是0，所以bar会返回1。foo(a)用到rand形参，会在a和b随机化之后被执行。返回结果取决于a的随机化结果。



# 2. issue collection
下面总结一些比较难以发现的constraint-randomize中的问题。

## 2.1 rand variable feedback with function in constraint 
对于上述的步骤4的函数(b)形式，有时我们会碰到这种写法,
~~~verilog
rand int a;

constraint csrnt {
  a == foo(a);
}
~~~

这种写法本身是有问题的。
上面对于constraint中的函数的函数使用已经做出了解释。等号右侧foo(a)中的a会先被解出，然后运行函数得到一个返回值，这个返回值又重新赋值给a。等于说是我们在赋值的同时否定了之前对a的随机结果，或者说这里做了对a的二次赋值。这对于constraint solver大多数时间是行不通的，会造成随机化失败，除非二次赋值的值恰好和第一次赋值一样。

解决办法:
我们先看一下这里这种写法的动机是什么。a == foo(a) 是一种类似于程序执行的写法，目的是利用a的原值去得到新值，然后更新a。
但是由于a的原值在constraint-randomize里不会被保存，而是被随机覆盖，目的是达不到的。
为了实现这种根据原值的更新，我们应该拆开来写，把第一部分a的随机化通过randomize得到。然后在post_randomize()中做第二步更新赋值。


## 2.2 misconception that randomize a single variable would affect other variables
这里是一个常有的误区，如果有两个有约束关联的rand型变量a和b，只随机化b，randomize(b)也可以把a随机化。
实际情况不是这样。randomize(b)只会随机化b，否则就和randomize()没任何区别了。

在SV中，obj.randomize(a,b,c) 给出形参列表时，它表示显式给出obj中要进行randomize的变量。无论是否变量被定义为rand，都会被强制作为rand。
未被加入形参列表的强制当作状态变量state variable，不参与随机化，只会保持原值。randc变量不遵循上述规则，作为randomize()形参时和没作为没区别。

除此之外，还有一个小点值得注意。定义为rand但被当做state variable的变量，虽然不会被随机化成别的值，但它仍会被放入constraint中进行校验。不在constraint范围内时仍然会报错。
比如下面的例子，  

~~~verilog
rand int a,b;

constraint csrnt {
  a < 0;
}

assert(randomize(b));
~~~

a不会参与随机化赋值，但a仍受constraint限制。由于a的初始值为0, 不满足a<0从而报错。


~~~verilog
rand logic[3:0] a,b;

constraint csrnt {
  b < a;
}

assert(randomize(b));
~~~

上面的例子里，a没有被随机化，a会被赋予初始值0. 而b随机化时，b只能是非负数，造成随机化失败。

解决办法:
理想的解决办法是先随机化a，再随机化b。但在变量多的时候显然一个个随机化不现实。简单的方法就是先随机化所有rand变量去起到一个初始化的作用，然后再单独随机化b。


## 2.3 randomization order of randc variables
看一个例子，
~~~verilog
randc int a, b;

constraing csrnt {
  a inside {[0:1]};
  b inside {[0:9]};

  a==0 -> b>=5;
  a==1 -> b< 5;
}
~~~

例子中用到了两个randc变量。对于randc变量，它有一个隐藏的约束条件，就是当前随机值不能和原值相同。
在LRM中，randc型变量会独立随机化，且相互随机化顺序并没有指明。这就会造成一个问题。
如果b先于a随机化，那么a会根据随机化结果得到一个值，而这个值由于是逆向从b推导出来的，没有考虑到a的randc隐藏约束条件。那么一旦a的随机值与原值相同，那么就会造成随机化错误。

但这个问题不是所有时候都会出现，有的仿真器会自动调节好随机顺序，有的不能。

解决办法:
solve a before b


## 2.4 bit width in array element
数组函数sum(), product()的随机化结果都是根据数组元素的位数大小决定的。
如果计算结果可见的位数的数值满足约束条件，随机化也会成功。

~~~verilog
rand bit arr[10];

constraint cst_1 {
  arr.sum() == 0;
}
~~~

sum()的做法是把数组所有的位加和并转化到1位上，即 1'(b[0] + ... + b[9]) == 0;
这就造成了一个舍位的问题，如果真实结果是6(3'b110)，最后一位还是0, 结果随机还是对的，但是分到每一位上，b有6位都是1.

解决办法:
利用item语法结合目标扩展位数，arr.sum() with (2'(item)) == 0;
它的效果是2'(2'(b[0]) + ... + 2'(b[9])) == 0. 它会把所有参与元素都转化成2位，包括计算结果。
这里可能会有一个疑问，数组元素扩展了位数，会不会把数组元素随机化到一个它不应该有的大值然后被钳位到定义的位数？
比如这里条件换成 2'(2'(b[0]) + ... + 2'(b[9])) == 2, 会不会某一个元素随机到2'b10, 其他元素全是2'b00, 最终结果也是2, 但2'b10是不应该出现的。会出现这种情况吗？
经试验，不会的，随机化的时候会把元素原位数考虑进去，不会有单个元素超界的现象。这里item的位数扩展只是对于计算结果有表达效果。

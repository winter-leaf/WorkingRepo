---
title: Some subtleties in SV
top: false
cover: false
toc: true
mathjax: true
date: 2021-05-29 13:03:37
password:
summary:
tags: SystemVerilog
categories: SystemVerilog
---


记录一些SV中容易忽略的小细节。
       
<!--- more --->

# 1. Real type conversion
real到int的转换采用小数部分四舍五入。
任何带有x,z的packed二进制值向real转换时，x,z都会被转化成0.


# 2. "\0" in String
string中出现的"\0" 会被自动当做空字符忽略.


# 3. enum
enum如果出现x或z的指定赋值，后续enum值必须赋值  
~~~verilog
  // Syntax error: IDLE=0, XX='x, S1=??, S2=??
  enum integer {IDLE, XX='x, S1, S2} state, next; 
~~~


# 4. Enumeration定义序列命名
可以用数组定义的形式定义index重复的enum名字。  
~~~verilog
  // 会延展成为 {add, sub0, sub1, ..., sub4, jmp6, jmp7, jmp8}
  typedef enum { add=10, sub[5], jmp[6:8] } E1; 
  E1 a = sub3;
  $display("a = %s", a.name()); // 输出sub3
~~~


# 5. $可以被当做实参传递  
~~~verilog
  parameter r2 = $;
  property inq1(r1,r2);
    @(posedge clk) a ##[r1:r2] b ##1 c |=> d;
  endproperty 
  
  assert inq1(3);

  // test if a constant is bound
  bit is_unbounded = $isunbounded(r2);
~~~


# 6. const和parameter/localparam的区别
const是仿真时间被确定的常数。parameter/localparam是编译时间被确定的常数。


# 7. automatic program中的变量作用域
即使program声明为automatic，automatic也只对内部的function，task，begin-end有效。
其他地方定义的变量等无效。  
~~~verilog
program automatic test ;
  int i; // not within a procedural block - static
  task t ( int a ); // arguments and variables within task t are automatic
    ...
  endtask 
endprogram 
~~~


# 8. type(variable_name | systemverilog legal data type)操作符
*type(variable\_name | systemverilog legal data type)* 操作符可用于类型转换和比较:  
~~~verilog
typedef enum {DOG=0, CAT=1, PIG} ani;
real a = 1;
ani b = type(b)'(a);
$display("b = %s", b.name()); // output is CAT

case(type(a)) inside
  type(int):  ......
  type(logic[1:0]):  ......
endcase
~~~


# 9. real值的二进制转换
*shortreal* 类型转换为32位数时，要想保留浮点数形式，应使用$shortrealtobits()。反之则用$bitstoshortreal(). 同样的, $realtobits()适用于*real*类型.  
~~~verilog
  shortreal a = 1.25;
  logic[31:0] b;
  b = a;
  $display("b = %b", b); // 00000000000000000000000000000001
  b = $shortrealtobits(a);
  $display("b=%b",b);  //00111111101000000000000000000000,sign=0,exp=127,mantisa=0100...
~~~


# 10. Associative array初始化  
~~~verilog
// 显式初始化
integer tab [string] = '{"Peter":20, "Paul":22, "Mary":23, default:-1 };

// Associative array 可以为未来生成的元素设定默认初始化元素值
int a[int] = '{default:1}; 
a[666]++; // a[666] = 1 -> a[666] = 2
~~~


# 11. Queue的几点注意事项
1. If (a > b) || (a<0 && b>=Q.size()), then Q[a:b] yields the empty queue {}.
2. Q[ a : b ] where a < 0 is the same as Q[ 0 : b ].
3. Q[ a : b ] where b > $ is the same as Q[ a : $ ].
4. 任何不以ref引导并以queue形式做形参的function/task都是传值而不是传地址。数组效果类似。


# 12. Array method using *with* condition  
## 12.1 sum of 2 dimensional array
~~~verilog
int q[2][2] ='{ '{5, 10}, '{15, 20} };
Int q_sum = q.sum() with (item.sum());
$display("q_sum= %0d", q_sum);
~~~

## 12.2 ‘item’ has attribute ‘index’
~~~verilog
int q[$] = '{11,1,13,3,15,16};
int p[$] = q.find() with (item.index == 4);
$display("p = %0p", p); // output is p = ’{15}
~~~


# 13. Interface class
## 13.1 哪些东西可以被继承
父类interface class中的_parameters_ 和 _typedef_ 是可以被子接口类interface class *extends*继承的，但不能被实现类*implements*继承。  
~~~verilog
  interface class A#(type T=int);
    typedef logic[1:0] logvec;
  endclass 

  interface class subA extends A#();
    pure virtural function T foo(logvec v);
  endclass

  class imp_A implements A#();
    logvec a; // ERROR, logvec is not defined
  endclass
~~~

## 13.2 interface class casting
接口类也可以以多态形式接受实现类实例。



# 14. Typedef class
由于代码书写顺序而不得不提前声明class时，有时会用*typedef class ClassName;* 的形式。
值得注意的是，对于参数化的类名，它*typedef*的形式与非参数化类时是一样的，并会不带参数化命名。
~~~verilog
  typedef class C;
  class C#(int a);
    ......
  endclass
~~~


# 15. Wait statement
一般情况下，wait()中是不能用函数的，因为函数只能在最开始执行wait的时候执行一次，如果结果为false就会一直等待。比如wait(foo())。
但是有一个例外，那就是函数是系统函数或者数据类型自带函数，比如wait($onehot())，wait(array.size())。这些函数wait是可以一直感知的。


# 16. iff 可以用在任何条件语句的逻辑表达式后  
~~~verilog
  always @( (a or b) iff en==1 ) begin
    ......
  end
~~~
iff 比 or 优先级高.


# 17. sequence can be used as an event
可以结合sequence和@，@结束时是在observed region。
其实sequence的本质就是一个systemverilog event，它也可用.triggered属性  
~~~verilog
  sequence abc;
    @(posedge clk) a ##1 b ##1 c;
  endsequence 

  initial begin 
    @ abc;
    $display( "Saw a-b-c" );
  end
~~~
 

# 18. disable
## 18.1 disable is only for task and named block
disable只可以用于task和named block，而不可以用于function。function中的named block除外。

## 18.2 disable works as continue in named block in for loop
disable作用于for loop中的named block时，它只会结束当前的循环，相当于continue。

## 18.3 disable name和return的区别:
disable name会把task或named block中的所有动作都结束掉。而return只会返回主线程，如果task里有其他并发的线程是会不被结束的。  
~~~verilog
  task automatic foo();
    fork      
      forever begin
        #5;
        $display("%0t", $time);
      end
    join_none
    
    begin
      #15;
      // return;  // 只会返回foo(), 上面的子线程还会继续运行
      // disable foo;  // 会把foo()中的所有动作都取消掉
    end
  endtask
~~~


# 19. Fine grained process control
## 19.1 usage example  
~~~verilog
  process proc;
  fork
    begin : my_proc
      proc = process::self(); // 得到 my_proc 的线程句柄
      do_thread_task();
    end
  join_none 
  wait(proc != null); // 等待my_proc被建立
  proc.await(); // 等待my_proc结束
  if(proc.status == FINISHED) begin
    $display(“my_proc ends”);
  end
~~~

# 19.2 process.kill()与disable fork的区别
process.kill()和disable named block效果一样，它把所有内部层级fork出来的线程也全部杀死。
disable fork只会杀死fork的第一层。



# 20. a/0和a%0
## 20.1 除数为0
SV中允许除数为0. 得出的结果永远是x。

## 20.2 取余时，被除数或除数为负数
若按照数学定义，余数必须是非负数。
但SV定义余数必须与被除数同号，这会造成余数为负的情况。按照数学定义这其实是不合理的。
这里SV的定义并没有完全按照标准的数学定义。


# 21. Increment and decrement operators race
~~~verilog
i = 10; 
j = i++ + (i = i - 1); 
上面代码执行后，j的值可能是18, 19, or 20，无法确定。因为不能保证++/--和+/-操作符的优先级 。
~~~

       
# 22. 小数求幂
SV允许小数求幂, real**N


# 23. Selective delay time
SV支持可变动delay. 形式为 #(10:20:40) output = 1'b0; // #(min : typical : max)
默认情况下仿真器使用typical值，可通过仿真器的runtime option动态更改.


# 24. Global clocking block
$global\_clock()采用的global clocking block一般取”就近向上”原则进行搜索，找到的第一个global clocking block会被采用。但是有一个例外情况，在sequence，property和checker里使用的$global\_clock()会从sequence，property和checker实例化的地方开始就近向上搜索，而不是从其定义的地方。  
~~~verilog
module top();
  sub sub0();
endmodule

module sub();
  logic clk_sub;
  logic req;
  global clocking cb_sub @(clk_sub); endclocking
  always @($global_clock) begin // 此处$global_clock采用的是cb_sub
    ... 
  end 

  // 此处是property的实例化，会就近采用global clocking block cb_sub
  assert property (subsub.p(req)); 
endmodule


module subsub();
  locig clk_subsub;
  global clocking cb_subsub @(clk_subsub); endclocking
  property p(a); 
    // 此处只是property的定义，并不会做采用任何global clocking block
    // 即使此module里定义了global clocking block也不会采用
    @($global_clock) a |=> !a; 
  endproperty 
endmodule
~~~


# 25. Pass/assign event handle
event可以互相赋值，赋值的效果是传递event handle。  
~~~verilog
  event a;
  event b;
  // a和b共享一个handle，此后a，b会等价触发。
  // 任何等待event的语句如@(event), wait(event.triggered)都是在
  // 等待相应event handle触发event。
  a = b; 

  fork 
    T1: forever @ E2; 
    T2: forever @ E1;
    T3: begin 
      E2 = E1;
      forever -> E2;
    end 
  join
~~~

上面的例子中触发E2是不会触发T1的，因为handle赋值发生在等待event之后。如果在fork之前赋值，T1是可以被触发的。


# 26. Assertion restriction
Restrictions are only used for formal verification as *assume*. Unlike *assume* is treated as *assert* in simulation, restrictions are completely ignored in simulation.   
~~~verilog
r1: restrict property (customized_property);
~~~




# 27. Large data copy in assertion  
~~~verilog
bit a;
integer b;
byte q[$];

property p2;
integer l_b;
($rose(a), l_b = b) |-> ##[3:10] q[l_b];
endproperty
~~~

这种runtime动态确定目标信号的形式很有可能造成整个q都被观测。应尽量避免这种形式。


# 28. use sequence like function
可以通过local inout/output的形参定义的方式使sequence具有改变实参的功能，类似于task/function.  
~~~verilog
sequence sub_seq2(local inout int lv);
  (a ##1 !a, lv += data_in) ##1 (data_out == lv);
endsequence

sequence seq2;
  int v1;
  // lv is initialized by assigning it the value of v1,
  // when the instance sub_seq2(v1) matches, v1 is assigned the value of lv 
  (c, v1 = data) ##1 sub_seq2(v1);
endsequence
~~~


# 29. Cross coverage  
~~~verilog
int i,j;

covergroup ct;
  coverpoint i { bins i[] = { [0:1] }; }
  coverpoint j { bins j[] = { [0:1] }; }
  x2: cross i,j {
    bins i_zero = binsof(i) intersect { 0 };
  }
endgroup
~~~

x2最终产生的产生的bin为: i\_zero, <i[1],j[0]>, <i[1],j[1]>
在cross中显式地定义一个bins并不会删除其他自动生成的bin，其他自动生成的bin还会保留，除非用ignore\_bin删除它们.



# Reference
1. systemverilog-IEEE.std.1800-2017

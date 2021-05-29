---
title: gotcha记录和总结
top: false
cover: false
toc: true
mathjax: true
date: 2020-07-16 19:46:27
password:
summary:
tags: gotcha
categories: SystemVerilog
---


记录和总结一下见到的个人觉得有启发的gotcha。

<!--- more --->

# 1.关于bit的迷思

## 1.1 位省略
先来看一个问题, 12'shFF和12'(8'shFF)的值一样吗？
既然这么问了，结果肯定是不一样。12'shFF的二进制结果是 000011111111，12'(8'shFF)的二进制结果是111111111111。
进一步想，'shFF的值是什么？
'shFF的二进制结果是0...00011111111。
这里到底发生了什么？

要明白这个问题，要先明白数值的字符表示是什么样的。
数值表示有如下格式:
[size]’[s]<base><value>，其中符号标志[size]及[s]可省略，[s]省略则表示为无符号数。
[size]表示最终这个数值表示的二进制位数。如果省略，则至少表示32位，这也是为什么上面的’shFF没有具体给出的0的个数。

在[size]’[s]<base><value>表示形式下，任何数值都是以无符号二进制表示的。base_value决定了的二进制数值大小。
负号”-”表示是否将二进制转换为补码形式。’s’表示编译器最终看待数值的方式，是以无符号数看待还是以有符号数看待。  
~~~verilog
$display("%b", -'d12);  // 11111111111111111111111111110100
$display("%d", -'d12);  // 4294967284
$display("%b", -'sd12); // 11111111111111111111111111110100
$display("%d", -'sd12); // -12
~~~


那么12’shFF就很好理解了，最终结果肯定是一个12位的有符号数。但是只给定了低8位数值，没有给定高4位，那高四位的值应该是什么？
这就涉及到位省略的问题。在verilog/systemverilog中，在给定整体位数且数值位数比整体位数低的情况下，高位不是x或z时，默认补0，高位是x或z时，默认补x或z。所以12’shFF中没有给定的高四位就是0.

## 1.2 位扩展
那为什么12'(8'shFF)的结果是111111111111？
这里涉及到位扩展的问题。8’shFF不涉及到任何位省略的情况，且是符号数，那么结果就是十进制的-1。关键在于之后12’()的扩展。
扩展是根据最高位定的。8’shFF的最高位是1，所以扩展后就是111111111111。

再想一个小问题, -12'shFF的结果是什么？
-12’shFF其实可以分成(-)和(12’shFF)两部分。那结果就很显而易见了是十进制的-255。

上面解释了位扩展，那么赋值的时候扩展是什么样的？比如 logic signed [7:0] a = 4’hF ?
赋值时的扩展遵循这样一个原则: 最终扩展位数根据左侧变量位数而定，扩展位的值根据右侧原变量最高位而定。
根据此原则，上面例子的最终结果就是a = 8’(4’hF) -> 00001111。

## 1.3 变量运算
如果是变量运算呢？形如 logic[3:0] a = 2’sh3 + 2’h2?
扩展位数的问题上面已经解释过了，仍然是看左侧的位数。主要问题是(signed number + unsigned number)的结果到底是个signed还是unsigned？
无符号数/有符号数的运算原则是(u=无符号，s=有符号，‘→’表示结果): u+u→u, s+s→s, u+s→u。
那么显然例子中a最终应该得到一个从右侧得来的无符号值，具体过程是这样的:
1. 检测到右侧是u+s，那么把所有的值都当做无符号数运算
2. 检测到左侧是4位宽度，对右侧进行位扩展4’(2’h3) + 4’(2’h2)
3. 计算得到临时无符号数结果4’h3+4’h2=4’h5
4. 由于最终是4位且给定数值是3位的h5，那么出现位省略的情况，直接高位补0，所以最终结果是a = 0101

这里提一个关于变量运算的小插曲
~~~
logic signed [3:0] a,b;
logic signed       cin;

a = 3;
b = 4;
cin = 1;
a + b + cin = ?
~~~
如果查看结果的话会发现a + b + cin = 6, 而不是预想中的8。
这是由于cin的符号性，由于cin是符号数，所以值1就代表了运算中十进制的-1，即结果是a+b+(-1)。
拆开来看，整个右侧都是符号数所以会对cin进行符号位扩展得到4’b1111，还是十进制的-1.
要想解决，就必须把-1变成+1，即更换符号位，但是cin只有一位，没办法再从自身改变。那么就只能手动补上一个符号位{1’b0, cin}。

## 1.4 位选取
位选取运算的结果永远是无符号的，即使从有符号数中位选也还是得到无符号数。
~~~
logic signed[3:0] a;
logic signed[4:0] b;
a = -1;
b = a[3:0];
~~~
即使我们没有对a做任何改变，但位选取运算使得a[3:0]得到一个符号数。最终b的结果不是-1，而是01111即十进制15。


# 2.异步条件优先级
看一个用于仿真测试的例子
~~~
always_ff(posedge clk, negedge rst_n, negedge set_n) begin
  if(!rst_n) begin
    q <= 1’b0;
  end else if (!set_n) begin
    q <= 1’b1;
  end else begin
    q <= d;
  end
end
~~~
仿真模型的逻辑意图很明显，实现异步的复位和置位工作。但这里面有一个坑，那就是它其实还含有一个优先级的仲裁机制。在复位期间如果置位也随后出现，那么复位会把置位的分支给取代掉。这样一来即使复位信号被取消且置位信号还是有效，由于没有触发事件，置位分支仍然不会马上被执行。直到有下一个时钟沿，置位分支才会被执行。

这里本质上我们要模拟的是一个latch，这个latch以rst_n和set_n作为敏感信号进行电平触发。
但从综合器的角度来看，latch和时钟沿数据更新的always_ff是不匹配的。而且在综合后我们想要做的也是时钟沿触发而不是电平触发，也就是说，等到下一个时钟沿再去置位是合理的结果。

但仿真模拟时，我们却需要latch来达到目的。

这里有两个方法:
一是压根就别在复位的期间进行置位，因为这本身就不符合正常用法。
二是如果真要在复位的期间进行置位，那么可以用下面的例子，但要区分这只用于仿真过程，而不用于综合。

~~~
`ifdef only_for_simulation
always @* begin
  if(rst_n && !set_n) begin
    force q = 1;
  end else begin
    release q;
  end  
end
`endif

always_ff(posedge clk, negedge rst_n, negedge set_n) begin
  if(!rst_n) begin
    q <= 1’b0;
  end else if (!set_n) begin
    q <= 1’b1;
  end else begin
    q <= d;
  end
end
~~~


# 3.enum默认初始值
~~~
enum {A, B, C} cur_st, nxt_st;

always_ff @(posedge clk) begin
  if(!rst_n) begin
    cur_st <= A;
  end else begin
    cur_st <= nxt_st;
  end
end

always @(cur_st) begin
  case(cur_st) inside
    A: nxt_st = B;
    B: nxt_st = C;
    C: nxt_st = A;
  endcase
end
~~~

这个例子中cur_st会永远的卡在A值上。
原因是enum的初始化问题。在不指定enum类型的情况下，enum默认会初始化到0，而0正好是列表中的第一个值。在例子中就是A，那么即使碰到了复位，值还是变到A，相当于没变化，那么后续的状态更新也就不会被触发。

要解决这个问题有三个方法:
1. 推荐方法，不要用always @(xx)的latch风格，而是用always_comb，always_comb会在仿真最开始的时候自动的激活一次。
2. 给enum加上类型，比如enum logic[1:0] {A,B,C}。类型的添加能使默认初始化值变到X。
3. 手动添加非零的值比如enum {A=1,B=2,C=3}。


# 4.missing event trigger
~~~
initial begin
  ->evt;
end

always @(evt) begin
  q <= 0;
end
~~~
上面的这段always代码有可能永远不会执行，原因是evt的触发在@(evt)之前，即在等待之前就触发了，从而到时错过event。
有两种方法可以解决:
1. 从触发角度解决，用#0->evt或者->>evt操作符来让触发延后一个delta cycle
2. 从等待角度解决，用wait(evt.triggered)


# 5.semaphore等待机制
~~~
semaphore s = new(3);

initial begin
  s.get(1); // A
end

initial begin
  s.get(1); // B
  #10ns;
  s.get(1); // C
end

initial begin
  #5ns;
  s.get(2); // D
  s.get(1); // E
end
~~~

上面这段代码的关键点是理解C和D。在步骤A和B中，它们同时在0时刻各自取得一个token，在5ns后D步骤试图取得两个token但没有足够的数量。所以D会等待直到token个数满足两个。重点是步骤C和E，C在另一个线程中且在时间上晚于D执行，但却可以先于D结束，因为C可以成功取得一个token。而E和D在同一线程，即使在5ns时有足够的token也不能先于D执行。

结论，同一线程中semaphore.get()的顺序执行，不同线程中的semaphore.get()独立执行且共享一个semaphore pool。


# 6. wire,reg,logic
reg和logic一样，只不过在systemverilog中reg有了相应的数据类型logic.
wire是net类型不能储值，而reg/logic可以。
wire可以有多驱动源，而reg/logic不可以。



# 7.消失的函数返回值
在verilog/systemverilog中，函数定义省略返回值时，默认返回值是logic。也就是说所有的返回值最终只会有LSB。
例如下面的例子，返回值是1而不是7.
~~~
  function foo();
    int a;
    a = 7;
    return a;
  endfunction
~~~


# 8. 带默认值的形参只能放在ref类型形参前吗？
如果这样定义和使用函数就会报错:
function void foo(ref int a, int b=0);

int x;
foo(x);

error message:
>Illegal connection to the ref port 'b' of function/task 'foo',formal 
>argument should have same type as actual argument.

为什么？难道函数还对形参位置敏感？
这其实是形参端口类型的问题。共有四个形参端口类型input, output, inout, ref。这四个类型都可以进行默认赋值。但在SV中默认省略端口类型时，省略类型与前一个相同，若没前一个则默认为input。
四个类型中只有input可以不进行实参传递，其他的类型本质上具有连接性，使用时必须进行实参传递。
那么上面的例子很显然是错误地认为b会当做input类型而省略实参传递。
解决方法: 把b也显式地进行赋值，foo(x, y);


# 9.消失的延时赋值语句
~~~
initial begin
  clk <= 0;
  forever #5 clk = ~clk;
end

assign #3 a = clk;
assign #6 b = clk;
~~~

运行上面的代码时会发现b永远不会变。为什么会这样？
要理解这个就要先明白两个概念，惯性延时和传输延时。
传输延时就是指先采样一个值，再经过特定的延时时间将其输出。
惯性延时就是指先采样一个值，并指定一个惯性时段，在惯性时段内如果输入再次发生变化则忽略前一个采样，采用新采样值，并重新计算惯性时段，直到某一个惯性时段内没有多次变化后结束后再将其输出。换句话说，给定一个时段，如果时段内出现两个值，取后面那个，并重新计时。这一般是为了滤除目的值之前的glitch。

例子中的assign #3和assign #6就是惯性延时。由于#6的惯性时段长于#5，在惯性时段内clk可以变换两次，那么取消#5前的采样并重新计时，再计时又是#6，又会碰到变换两次的clk，一直延续下去。b永远不被赋值。

解决办法就是换成传输延时:
~~~
always @(clk) begin
  b <= #6 clk;
end
~~~


# 10.任务被自己侵犯了
~~~
module tb;
  task foo(string name, int n);
    repeat(n) begin
      #10ns;
      $display("time = %0dns, name = %0s", $time, name);
    end
  endtask
  
  
  initial begin
    fork
      begin
        foo("kkk", 6);
      end
      begin
        #25ns;
        foo("qqq", 6);
      end
    join
  end
endmodule
~~~

如果执行上面这段代码会有如下输出:
> time = 10ns, name = kkk
> time = 20ns, name = kkk
> time = 30ns, name = qqq
> time = 35ns, name = qqq
> time = 40ns, name = qqq
> time = 45ns, name = qqq
> time = 50ns, name = qqq
> time = 55ns, name = qqq
> time = 60ns, name = qqq
> time = 65ns, name = qqq
> time = 75ns, name = qqq
> time = 85ns, name = qqq

结果表示从第二个线程真正开始运行任务后，第一个线程的任务的内容竟然被第二个线程任务覆盖了。这怎么回事？

原因是因为任务的定义是static静态的。如果定义成task automatic或者直接放在class里就能正常输出。
static的任务会共享一个函数/任务地址空间。上面的代码相当于对一个正在执行的任务动态改变了形参。
第一个线程会在一开始采样形参n的值，执行6次循环，每次重新读取形参name的值。
第二个线程会在25ns后采样形参n的值，也执行6次循环，每次重新读取形参name的值。
形参n的值是一开始就采样好的，不会受影响，但形参name是每次都重新读取。那么就会受影响。


# 11.误杀
disable xxx语句用于结束在当前层级空间中以xxx命名的所有线程。
层级可以是module，program，class等等。
xxx可以是任务名，也可以是语句块的名字。

这可能会造成意图杀死一个特定线程的同时，误杀共享同一命名的各个线程。
解决方法就是要分别命名。


# 12.assertion竟会自己活过来
concurrent assertion被放在if-else中，即使条件为假，assertion也会被激活。
~~~
property pty();
  @(posedge clk)
  b |-> (c>0);
endproperty

always @(posedge clk) begin
  if(a) begin
    assert(pty) $display(“assertion evaluated”);
  end
end
~~~

代码逻辑很直接，但问题是即使a为0，assertion也会被激活。
这是因为对于被if-else做先导的concurrent assertion，先行算子其实有两个，一个是if另一个是property中的先行算子。
在例子中就是a && b。在a=0的情况下，实际上是一个vacuous success。
所以if-else并不能过滤掉assertion的激活。


# 13.永远等不到的property
~~~
property p;
  @(posedge clk)
  a |→ #[1:$] b ##1 c
endproperty
~~~
根据上面的property定义，如果有一个这样的序列: a → 10 clk → b → 2 clk → c，它会检测到b和c之间两周期的错误吗？
答案是不会的。为什么这样？
这个property实际上是在看检测这样一个序列: a |-> #[1:$] (b ##1 c)
这么一看就比较清楚了，它只是在等待一个(b ##1 c)的出现，如果出现了(b ##2 c)那根本不关心，因为不是想要等的。

解决办法有两个:
1. 把(b ##1 c)拆开，分成(a|-> #[1:$] b)和(b |-> ##1 c)两个就可以了
2. 用[->1]操作符代替#[1:$] (b ##1 c)

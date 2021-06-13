---
title: Clocking block
top: false
cover: false
toc: true
mathjax: true
date: 2021-06-03 22:37:11
password:
summary:
tags: SystemVerilog
categories: SystemVerilog
---

clocking block的使用总结和几篇相关文章的笔记。

<!--- more --->

clocking block主要用于模拟对于一个信号的驱动和采样时间间隔，类似于设定setup/hold time。
对于一个信号，尤其是驱动或采样分别在module和class两侧时，不加时间间隔地同时进行驱动和采样会造成竞争冒险。
为了解决这个问题，应在驱动和采样时加以延时。假如我们在时钟上升沿来时，同时进行驱动和采样的基础上加上延时就有如下逻辑:  

~~~verilog
always @output_signal_from_dut begin 
  sampled_signal_value_before_change <= #t_setup output_signal_from_dut;
end
always @(posedge clock) begin 
  sampled_value = sampled_signal_value_before_change; 
  input_signal_to_dut <= #t_hold new_value; 
end
~~~

如果每次做采样和驱动的时候都人为地为每个信号都加上延时显然麻烦而且信号多了肯定不现实。clocking block就是为了简化这个过程而存在的。
clocking block一般且非常推荐定义在interface里，这样clocking block就天然地和interface绑定。虽然clocking block也可以定义在module等地方，但关联性不强，并不推荐。
clocking block是针对于同步信号的。对于异步信号，clocking block并不适用。

假定有一interface，其内部clocking block有如下定义结构:  

~~~verilog
interface intif();
  clocking cb_name @(posedge clk);
    default input #n output #n;
    input  [edge #n] signal_a;
    output [edge #n] signal_b;
  endclocking
endinterface
~~~

# 1. clockvar and clocksignal  
> clocksignal指intif.signal_a。
> clockvar指intif.cb_name.signal。

这两个概念是不一样的。clocksignal本身就是一个正常的信号，和定义在正常module里的信号没区别，可以被nonblocking assignment(<=)驱动和采样。clockvar本身是一个具有延时属性的信号数值，类似于上面例子中的(sampled_signal_value_before_change) 和(#t_hold new_value)。
clockvar本身是带有延时属性的，采样和驱动都会相对于clock有一定程度的偏移。
clockvar的采样用”=”符号，驱动用”<=”符号，虽与blocking/nonblocking assignment形式相同但含义不同。这里”=”, ”<=”在上下文是clockvar时只表示采样和驱动。
任何其他形式的赋值符号都应报错。但根据仿真器不同可能有实现上的遗漏，经实验VCS2020会遗漏采样时使用”<=”的报错情况。

# 2. 0 setup time and 0 hold time in clocking block
clocking block中任何非零的input setup time都会使得采样时间相对于当前时钟沿提前，即采样到上一个周期的数值。
但也可以是#0。与非零值不同，在这里#0是把采样时间延后到当前周期的observed region。
这样造成的最终效果是采样到的值为当前周期的信号新值，而不是上一个周期的值。这种用法与正常的采样概念相悖，不推荐使用。

类似的，clocking block中的hold time也可以定义为0, output #0。这样做会把驱动时机延后到Re-NBA region，而不是类似于nonblocking assignment一样在NBA region。虽然这样做不会在驱动功能上造成于采样的race，但在波形上并不会看到任何后置于时钟沿的输出信号偏移，不推荐使用。


# 3. ##0 and default clocking block
default clocking block指利用default关键字定义的clocking block。
##n指在非class情况下的对default clocking block进行n次等待。相当于:
repeat(n) @(default intif.cb_name)。
但是当n=0时，意在等待__下一个default clocking block__的发生。如果下一个default clocking block已经在其他线程或由于其他原因已经被触发，则##0无效且跳过等待。相当于:
wait(default clocking block triggered at current time slot);


# 4. inout signal in clocking block
inout类型的型号相当于具有单独的input和output属性。采样和驱动对应input和output属性，且互相独立。


# 5. clockvar direction in clocking block
LRM中提到clocking block中input clockvar不能被驱动，output clockvar不能被采样。
这样很多时候想在BFM里读上一个周期的输出值就很麻烦，由于不能直接读，必须在上一个周期驱动新值的时候同时把这个新值放到一个没有方向限制的临时变量里，以便于下一个周期读取，相当于曲线救国。
这无形中就增加了很多麻烦。
既然output clockvar不能直接操作，那么读clocksignal就可以了。因为我们只是用clockvar来驱动信号，并不会直接驱动clocksignal。最终clocksignal的值会等待clocking block的hold time来进行更新。


# 6. Several recommendations based on reference articles
1. When using a clocking block, the testbench should drive interface via its clockvars and should not drive the clocking signals directly after first clocking event of clocking block.
注: [2]建议一直使用clockvar驱动且永远不要使用clocksignal驱动。[3]建议初始化使用clocksignal。个人认为，既然clocking block是针对同步信号而言，在第一个同步时钟来临前，任何对clocksignal的直接操作都是不影响后续同步信号操作的，可以对其驱动。

2. Testbench code should synchronize itself to a clocking block’s clock event by waiting for the clocking block’s own named event, __NOT__ by waiting for the raw clock event. 

3. Write to output clockvars using the clocking drive operator __<=__. Never try to write an output clockvar using simple assignment __=__.

4. Use input __#1step__ unless you have a special reason to do otherwise. It guarantees that your testbench sees sampled values that are consistent with the values observed by your SystemVerilog assertions, properties and sequences.  
注:关于1step的概念，可以参照之前写的另一篇文章[SV time slot scheduling](https://winter-leaf.github.io/SV-time-slot-scheduling)

5. Use non-zero output skew values in your clocking blocks to make waveform displays clearer, and to avoid problems caused by clock network delays in gate level simulation. 

6. Never use input #0 in your clocking blocks unless you want to sample new value in current cycle via clocking block.
注: 参照上述小节2

7. Avoid the use of edge specifiers to determine clocking block skew.
注: 在clocking block为各个信号添加各自采样沿的方法可以被下列方法取代:
1) 延长setup/hold time或2)建立新采样沿的clocking block

8. Use your clocking block to establish signal directions with respect to the testbench. Do not add the raw signals to a testbench-facing interface's modport unless the raw signal is not in clocking block and is asynchronous signal.

# 7. Reference
[1] systemverilog-IEEE.std.1800-2017
[2] Bromley, J., Johnston, K.. Taming Testbench Timing: Time’s Up for Clocking Block Confusions. SNUG2012.
[3] Clifford E. Cummings. Applying Stimulus & Sampling Outputs‐UVM Verification Testing Techniques. SUNG2016.

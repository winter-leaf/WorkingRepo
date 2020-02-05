---
title: what is in uvm callback
top: false
cover: false
toc: true
mathjax: true
date: 2020-02-05 04:23:53
password:
summary:
tags: UVM
categories: SystemVerilog
---

# 1. usage of uvm_callback
<!---more--->
uvm_callback使用步骤:
1. 得到使用callback许可: 通过继承uvm_callback类，建立一个wrapper类
~~~
class callback_wrapper extends from uvm_callback;
  `uvm_object_utils(callback_wrapper)
  function new (string name);
    super.new(name);	
  endfunction
endclass : callback_wrapper
~~~

2. 在wrapper类中定义要执行的函数，如果要定义wrapper类的话，必须是virtual以便于子类实现
~~~
class callback_wrapper extends from uvm_callback;
  `uvm_object_utils(callback_wrapper)
  function new (string name);
    super.new(name);	
  endfunction
	
  virtual task/function foo(); 
  endtask/function
	
  virtual task/function var(); 
  endtask/function
endclass : callback_wrapper
~~~

3. 具体实现callback: 继承wrapper类，并实现执行函数
~~~
class real_callback extends callback_wrapper; 
  `uvm_object_utils(real_callback)
  function new (string name);
    super.new(name);	
  endfunction

  virtual task/function foo(); 
    ......
  endtask/function
	
  virtual task/function var(); 
    ......
  endtask/function
endclass: real_callback
~~~

4. 实例化，注册并加入callback到目标类中
~~~
class Driver extends uvm_component;
  `uvm_component_utils(Driver)
  `uvm_register_cb(Driver, callback_wrapper)

  function new (string name, uvm_component parent);
    super.new(name,parent);
  endfunction
endclass: Driver

module test;
  initial begin
    Driver drv;
    real_callback cb;
    // assuming there are more callback defined
    real_callback_1 cb_1;
    real_callback_2 cb_2;
    ...
    real_callback_n cb_n;

    drvr = new("drv");	
    cb_1 = new("cb_1");
    cb_2 = new("cb_2");
    ...
    cb_n = new("cb_n");

    // the callbacks execution order follows the order being added
    uvm_callbacks#(Driver, callback_wrapper)::add(drvr,cb);
    uvm_callbacks#(Driver, callback_wrapper_1)::add(drvr,cb_1);
    uvm_callbacks#(Driver, callback_wrapper_2)::add(drvr,cb_2);
    ...
    uvm_callbacks#(Driver, callback_wrapper_n)::add(drvr,cb_n);
		
    run_test();
  end
endmodule
~~~

5. 使用callback
~~~
class Driver extends uvm_component;
  task run_phase(uvm_phase phase);
    ...
    `uvm_do_callbacks(Driver, callback_wrapper, foo());
    ...
  endtask;
endclass: Driver
~~~
从上面的步骤可以简单看出来，uvm_callback的使用过程需要继承两层，这其实是很奇怪的一件事。一般情况在面对对象的概念下，基类中会实现通用的基本功能，具体实现会留给子类，那么继承一次就好了，为什么要继承两次并建立一个wrapper类? 只好看看源码，试图找一找答案了。

# 2. analysis
## 2.1 uvm_register_cb(T,CB) macro
这个宏用于注册，是一切的开始，它的展开如下:
~~~
`define uvm_register_cb(T,CB)
  static local bit m_register_cb_``CB = uvm_callbacks#(T,CB)::m_register_pair(`"T`",`"CB`");
~~~
本质上，它是声明了一个以callback字符串为后缀名的变量。这个变量的值由m_register_pair函数返回。m_register_pair的定义如下:
~~~
  static function bit m_register_pair(string tname="", cbname="");
    this_type inst = get();

    m_typename = tname;
    super_type::m_typename = tname;
    m_typeid.typename = tname;

    m_cb_typename = cbname;
    m_cb_typeid.typename = cbname;

    inst.m_registered = 1; 

    return 1;
  endfunction
~~~
撇开这里面的一系列变量，它整体上干的活其实就是一些变量值的记录，这些变量大多是用于进行存在性和类型检查以及输出更精细的调试信息，比如在重复callback注册时会告知是哪个目标类的哪个callback被重复注册。这其实很类似factory的一个注册过程，换句话说，uvm_callback在内部实现了一个工厂机制。这个注册过程会建立一个类型T和与callback之间的映射。


## 2.2 uvm_callbacks#(T, CB)::add();
这是uvm_callback机制中的第二步，用于给具体的目标类添加真正的callback实现。这个函数的具体声明如下:
~~~
static function void uvm_callbacks #(type T=uvm_object, type CB=uvm_callback)::add(T obj, uvm_callback cb, uvm_apprepend ordering=UVM_APPEND);
~~~
第一个参数obj表示要被添加callback的目标类。
第二个参数cb表示要添加的callback。
第三个参数ordering表示有多个callback时的执行顺序。

在源码中有这样一段注释: 参数obj并不是必须的，可以为null。cb必须提供，不能为null。参数ordering可以根据需要自行修改。若重复添加一个callback会收到警告信息。类的参数化列表中CB是可选项，uvm_callbacks#(my_comp)::add(comp_a, cb); 和 uvm_callbacks#(my_comp, my_callback)::add(comp_a,cb); 是一样的。

如果结合源码，再察看这段注释我们可以发现这个add()的添加过程会先进行注册信息检查，后进行数据记录。不同的给定实参，有不同的存储方式。
1. 如果obj=null，会向m_tw_cb_q这个队列中存放要添加的callback。m_tw_cb_q是一个uvm_queue#(uvm_callback)类型的对列。这里的"tw"表示typewide。
2. 如果obj给定了具体的目标类对象，会向m_pool中目标类对象所对应的队列中存放要添加的callback。m_poll是一个uvm_pool#(uvm_object,uvm_queue#(uvm_callback))类型的联合数组，这个数组中的各元素是以uvm_object为key，uvm_queue#(uvm_callback)为值的键值对。

回想调用add()的过程，我们一般用的形式是uvm_callbacks#(ClassType, CallbackType)::add(CompInst, CallbackInst)，根据上面说的，这里会向m_pool[CompInst].uvm_queue中添加CallbackInst实例。也就是说只有CompInst会看到并使用这个CallbackInst，即是实例相关的。
但如果我们把obj设为null，那么形式是uvm_callbacks#(ClassType, CallbackType)::add(null, CallbackInst)，此时会向uvm_typed_callbacks#(ClassType)的m_tw_cb_q添加CallbackInst。这里的CallbackInst会对整个ClassType可见，即此时是类型相关的。

到这里我们可以知道，add()的真正目的是通过控制obj的值，向可见域不同的地方加入callback实例，这里的可见域分为实例可见和类型可见。在具体调用的时候，实例可见的有优先级，如果同一CallbackInst被同时加入了两个可见域，那么实例可见的会被执行。

再回过头来看uvm_callbacks#(ClassType, CallbackType)这个类型。根据上面的注释描述，CallbackType可以忽略，那么可以这么理解:
1. uvm_callbacks#(ClassType [,CallbackType])的含义是: 关于ClassType这一类型的uvm_callback实例存储空间。
2. uvm_callbacks#(ClassType [,CallbackType])::add(*, CallbackInst)的含义就是: 向ClassType的callback存储空间中添加一个CallbackInst实例，此实例只对*可见。

上面看到的过程相对容易理解，大体上就是一个队列添加的过程。不太清晰的是各个类的定义和这些队列的关系。
callback相关类的继承关系如下:
uvm_object <— uvm_callbacks_base <— uvm_typed_callbacks#(T) <— uvm_callbacks#(T, CB)
uvm_object <— uvm_callback

从这个继承关系来看，uvm_callback***S***这一支与uvm_callback没什么直接关系。uvm_callbacks更像是一个容器类，内部存放着各种用于存放类似于uvm_pool这样的数组和队列。
m_pool声明于uvm_callbacks_base中，用于存放各种有具体实例对应的队列，可以被全局访问。
m_tw_cb_q声明于uvm_typed_callbacks#(T)中，用于存放无具体实例的队列，每个uvm_typed_callbacks#(T)都有一个属于自己的m_tw_cb_q，可以被全局访问。

到这里其实我们知道，uvm_callback使用过程中的wrapper类并不是必须的，因为add()函数并不会区别是子类还是父类的uvm_callback实例。同时，空壳wrapper只是提供了一个用于多态的API框架。wrpper的加入只是提供了更多的覆写实现的灵活性。如果不需要多余的灵活性，在wrapper类中实现具体函数并在add()函数中加入wrapper类的实例也可以在队列中添加元素，从而实现类似的效果。
简单来说，第一步从uvm_callback类继承是必须的，这是为了加入队列时的函数参数类型匹配。同时，uvm_callback并没有提供具体函数，所以我们要再添加一些要用的函数，这是第二步做的事情，但具体的函数实现是否在这个子类中实现看具体的灵活性要求。

## 2.3 a simple guess
uvm_callbacks#(T, CB)这个类的加入从功能上讲，其实有一定程度的多余，本质上，它就是将T与CB进行绑定注册，不同的(T，CB*)组合有不同的绑定记录。我们可以在uvm_typed_callbacks#(T)中构造一个注册函数，其参数就是CB，以达到这中一对多的绑定注册的效果。个人猜测，uvm_callbacks#(T, CB)的加入是为了更方便的编写注册宏定义，以及功能上的层次感。它把所需要的信息都放入参数化列表，在编译的时候直接使用宏定义，可以更直观的看出注册时地绑定关系。


---
title: UVM tree~tree~tree
top: false
cover: false
toc: true
mathjax: true
date: 2020-01-29 06:39:15
password:
summary:
tags: UVM
categories: SystemVerilog
---


UVM中的uvm_componet会以树状结构建立起来，每当调用工厂机制下的uvm_component::type_id::create(name,parent)，便会在UVM组件树中增加一个子结点。
<!---more--->

# 1. instantiate uvm_root
UVM树只有一棵，有唯一的根结uvm_root. uvm_root由单一实例化模式(建立时会检查是否已存在)保证其唯一性。
想要获得uvm_root实例，可以使用其静态函数uvm_root::get(). uvm_root没有父结点，任何没有明确指明父结点(parent=null)的uvm_component都会挂接在uvm_root下，作为叶结点。

uvm_root本身也是uvm_component的一个子类，自然而然在实例化时，也会调用super.new(name, parent)函数，但是uvm_root没有父结点，所以会传入parent=null。但仅仅这样是不够的，因为单传入parent=null和构建正常的叶结点没有区别。所以uvm_root.new()函数会在name这一参数上做文章，传入name="\_\_top\_\_"。同时在uvm_component.new()中会对传入参数配合做出判断，如果(name=="__top__" && parent=null)，说明当前要建立的结点是root结点，那么uvm_component.new()不会作任何操作，真正的root建立由X来做，X后续会说明。否则，就正常建立叶结点。

这里的X是uvm_root一个成员函数m_uvm_get_root()，是一个供外部调用的API，用来建立uvm_root实例。为了解决一开始，没有任何实例的情况下无法调用成员函数的问题，m_uvm_get_root()被定义为静态函数，可以直接被调用。

简单来说，根节点的建立过程是一个uvm_root和父类uvm_component配合实现的过程。
1. 程序的开始阶段，uvm_root的静态成员函数m_uvm_get_root()被外部调用，根节点实例被建立。
2. uvm_root会惯例性地调用uvm_component.new()，为了不重复建立根节点，会传入name="__top__" && parent=null以通过实例建立。
3. 当非根节点建立并调用uvm_component.new(name!="__top__" || parent!=null)时，uvm_component.new()会正常建立新的叶结点并挂接在UVM树上。


# 2. handle propagation between base nodes and subnodes
父子结点的连接情况和传统构建树的算法有一点小区别。以二叉树为例，一般建立只会在结点中存放左右两个子结点的指针，而不存放父结点的指针，徧历过程也大多是从上到下或层级展开。但在UVM树中，父结点handle会传给子结点，从而在子结点中可以对父结点进行操作。和uvm\_default\_factory类似，在uvm_component中有两个联合数组:

> uvm_component m_children[string]
> uvm_component m_children_by_handle[uvm_component]

分别以组件名和组件handle作为key，以组件实例作为值。这两个联合数组会用来保存当前结点对应子结点的信息。
值得注意的一点是，这里在存放时也用到了多态，如果想使用从这两个数组中拿出来的元素所含有的独有变量或成员函数，需要做一下downcast。

父结点中有m_add_child(uvm_component child)成员函数，用于向上述两个联合数组添加元素。




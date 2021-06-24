/*
 * 本文件包含三个部分：
 *
 * 1.基于cas、cas2的无锁队列
 * 2.防止ABA问题的内存回收算法
 * 3.测试代码（多生产者，多消费者）
 * 
*/
#include <iostream>
#include <chrono>
#include <unistd.h>
#include <stdint.h>
#include <pthread.h>
#include <stdlib.h>
#include <set>

using namespace std;
using namespace chrono;

/*
 * double cas 指针
 * 作用：同时更改32bit指针和32位count，是原子操作，不可被打断
 * 用于：1 基于链表的消息队列的插入和删除要用
 *      2 克服ABA内存问题的算法要用
*/
#if __SIZEOF_POINTER__ == 4
	/* 32位系统 */
template<typename T,unsigned N=sizeof (void *)>
struct DPointer {
public:
   /*
    * ---uiH---|---uiL---   (64bits)
    * ---ptr---|---cnt---   (64bits)
   */
   union {
       uint64_t ui;
       struct {
           T* ptr;
           size_t count;
       };
   };

   DPointer() : ptr(NULL), count(0) {}
   DPointer(T* p) : ptr(p), count(0) {}
   DPointer(T* p, size_t c) : ptr(p), count(c) {}

   /*
    * 指针与cnt同时cas
    * cmp：比较值 nval：期望值
   */
   bool cas(DPointer<T,N> const& nval, DPointer<T,N> const & cmp)
   {
       bool result;
       __asm__ __volatile__(
                   "lock cmpxchg8b %1\n\t"
                   "setz %0\n"
                   : "=q" (result)
                   ,"+m" (ui)
                   : "a" (cmp.ptr), "d" (cmp.count)
                   ,"b" (nval.ptr), "c" (nval.count)
                   : "cc"
                   );
       return result;
   }

   bool operator==(DPointer<T,N> const&x) { return x.ui == ui; }
};
#elif __SIZEOF_POINTER__ == 8
	/* 64位系统 */
template<typename T,unsigned N=sizeof(uint64_t)>
struct DPointer  {
    public:
    union {
        uint64_t ui[2];
        struct {
            T* ptr;
            size_t count;
        } __attribute__ (( __aligned__( 16 ) ));
    };

    DPointer() : ptr(NULL), count(0) {}
    DPointer(T* p) : ptr(p), count(0) {}
    DPointer(T* p, size_t c) : ptr(p), count(c) {}

    bool cas(DPointer<T,8> const& nval, DPointer<T,8> const& cmp)
    {
        bool result;
        __asm__ __volatile__ (
                    "lock cmpxchg16b %1\n\t"
                    "setz %0\n"
                    : "=q" ( result )
                    ,"+m" ( ui )
                    : "a" ( cmp.ptr ), "d" ( cmp.count )
                    ,"b" ( nval.ptr ), "c" ( nval.count )
                    : "cc"
                    );
        return result;
    }

    // We need == to work properly
    bool operator==(DPointer<T,8> const&x)
    {
        return x.ptr == ptr && x.count == count;
    }
};
#endif

/*一个普普通通的示例消息类*/
class Msg
{
public:
    Msg(){}
    int value;
    void msgSetValue(int value){ this->value = value;}
    int msgGetValue(){return this->value;}
};



#define THREAD_NUM 50           //生产者线程/消费者线程的数量
#define produceNUM 10000        //每个生产者线程/消费者线程的要处理的msg的数量

/*
 * 测试用的数据组织:
 * try插入msg时间点
 * 插入msg成功时间点
 * 测试数据
 * 取出msg成功时间点
*/
struct tst{
    chrono::steady_clock::time_point enqueueStartTime;
    chrono::steady_clock::time_point enqueueEndTime;
    int message;
    chrono::steady_clock::time_point dequeueTime;
}s[THREAD_NUM * 2 +10][produceNUM];



template<typename T>
class Queue
{
public:
    struct Node;
    typedef DPointer<Node,sizeof (size_t)> Pointer;

    enum { MG = 1000};                      //guard最大的个数，和并发量有关
    bool GUARDS[MG];                        //true代表guard被占，false代表guard可以回收
    int MAXG;                               //运行时，有效的guard数量，注意此数只增不减
    Node * POST[MG];                        //guards守护的node地址（防止被释放）
    Pointer HNDOFF[MG];                     //被“推卸责任”的node地址，代表可以被释放了


    struct Node
    {
        T           value;                  //值
        Pointer     next;                   //指针

        Node() : next(NULL) {}
        Node(T x, Node* nxt) : value(x), next(nxt) {}
    };

    Pointer       Head, Tail;               //队列的头和尾 tail插入，head取出

    Queue():MAXG(0) {
        Node * node = new Node();
        Head.ptr = Tail.ptr = node;         //空状态：同时指向一个无效dummy，主要好判断

        for(int i = 0; i < MG; i++){        //初始化
            GUARDS[i] = false;
            POST[i] = NULL;
            HNDOFF[i] = Pointer(NULL);
        }
    }

    /***************************队列API*******************************/
    void push(T x){
        Node * node = new Node(x,NULL);
        Pointer       tail, next;

        do {
            tail = Tail;                //快照
            next = tail.ptr->next;

            if (tail == Tail) {
                if (next.ptr == NULL) {
                    if (tail.ptr->next.cas(Pointer(node,next.count+1),next))
                        break;
                } else {
                    Tail.cas(Pointer(next.ptr,tail.count+1), tail);
                }
            }
        } while (true);

        Tail.cas(Pointer(node,tail.count+1), tail);
    }

    bool take(T& pvalue) {
        Pointer       head, tail, next;

        std::set<Node *> vs;
        int g = HireGuard();

        do {
            head = Head;
            tail = Tail;
            next = head.ptr->next;

            PostGuard(g, head.ptr);

            if (head == Head)   //指针和引用次数是一致的，说明其他线程没有更改
            {
                if (head.ptr == tail.ptr) {
                    if (next.ptr == NULL){
                        FireGuard(g);
                        return false;
                    }
                    Tail.cas(Pointer(next.ptr,tail.count+1), tail);
                } else {
                    pvalue = next.ptr->value;
                    if (Head.cas(Pointer(next.ptr,head.count+1), head))
                        break;
                }
            }
        } while(true);

        FireGuard(g);               //只是要g数量不要太大，并不是不trap
        vs.insert(head.ptr);
        vs = liberate(vs);
        for(typename std::set<Node *>::iterator it=vs.begin() ;it!=vs.end();it++)
        {
            delete *it;
            //std::cout << *it << std::endl;
        }

        //delete(head.ptr);
        return true;
    }


    /*************************预防ABA问题的API*******************************/
    /*
     * guards[]和MAXG是共享数据结构，MAXG保存曾经的最大值
    */
    int HireGuard(){
        int i = 0, max;
        while(!__sync_bool_compare_and_swap(&GUARDS[i],false,true))     //定位false，搜索可用guard
            i++;

        while((max = MAXG) < i)
            __sync_bool_compare_and_swap(&MAXG, max, i);

        //std::cout << "MAXG" << MAXG << std::endl;
        return i;
    }
    void PostGuard(int i, Node * v){        //对于要守护的node，进行保护（每个线程的i唯一，不用cas）
        POST[i] = v;
        return;
    }
    void FireGuard(int i){                  //解除guard （每个线程的i唯一，不用cas）
        GUARDS[i] = false;
        return;
    }
    /*
     * 每个线程决定要释放的node，放入vs中，统一由liberate进行仲裁可否释放
    */
    std::set<Node *> liberate(std::set<Node *> vs){
        int i = 0;
        while (i <= MAXG) {
            int attempts = 0;
            Pointer h = HNDOFF[i];
            Node * v = POST[i];

            if(v != NULL && vs.find(v) != vs.end()){      //遍历所有guards，找到自己相关的v gs
                while (true)
                {
                    if(HNDOFF[i].cas(Pointer(v,h.count+1),h)){
                        vs.erase(v);
                        if(h.ptr != NULL) vs.insert(h.ptr);
                        break;
                    }
                    attempts++;
                    if(attempts == 3) break;
                    h = HNDOFF[i];                          //重新快照
                    if(attempts == 2 && h.ptr != NULL) break;
                    if(v != POST[i]) break;
                }
            }
            else
            {
                if(h.ptr != nullptr && h.ptr != v)
                    if(HNDOFF[i].cas(Pointer(NULL,h.count+1),h))
                        vs.insert(h.ptr);
            }
            i++;
        }
        return vs;
    }

};

/********************************************************************************/

Queue<Msg> * mq = NULL;                     //全局queue

/***********************************测试用API**************************************/
volatile bool testStart = false;            //volatile防止被编译器优化！

void * produce(void * data){
    int id = pthread_self();        //获取id
    Msg msg;

    while (!testStart) {}

    for(int i = 0; i < produceNUM; i++)
    {
        s[id][i].enqueueStartTime = chrono::steady_clock::now();  //now()不是线程安全的
        msg.msgSetValue(s[id][i].message);
        mq->push(msg);
        s[id][i].enqueueEndTime = chrono::steady_clock::now();

        if(i == produceNUM - 1){
//            std::cout<<"thread "<<id<<"Sleep"<<std::endl;
//            sleep(1);
//            std::cout<<"thread "<<id<<"Wakeup"<<std::endl;
            //i = 0;
            //break;
        }
    }
    return NULL;
}
void * consume(void * data){
    Msg res;
    bool bres = false;
    int i = 0;
    int id = pthread_self();

    while(1)
    {
        bres = mq->take(res);
        if(bres == true){
            s[id][i].dequeueTime = chrono::steady_clock::now();  //记录clock
            s[id][i].message = res.msgGetValue();
            //printf("the msg: %d\n",res.value);
            i++;
        }

        if(i == produceNUM){
            return nullptr;
            i = 0;
        }
    }
}

void * testControl(void * data){
    //读取回车，并且testStart = true 其他线程检测到后，开始投放消息
    //cin.get();
    testStart = true;
    //此线程退出
    return NULL;
}
 
int main()
{
    pthread_t threads[THREAD_NUM];          //生产线程
    pthread_t threads1[THREAD_NUM];         //消费线程
    pthread_t threadsTest;                  //测试用线程

    int flag = 0;                           //测试用flag
    int num = 0;
    mq = new Queue<Msg>();                  //实例化队列

    for(int i = 2; i < THREAD_NUM + 2; i++){
        for(int j = 0; j < produceNUM; j++){
            s[i][j].message = num++;//rand();               //测试数据：随机数
        }
    }

    for(int i = 0; i < THREAD_NUM; i++){
        pthread_create(&threads[i], NULL, produce, NULL);
    }
    std::cout << "create produce threads : "<< THREAD_NUM << " OK"<< std::endl;

    for(int i = 0; i < THREAD_NUM; i++){
        pthread_create(&threads1[i], NULL, consume, NULL);
    }

    pthread_create(&threadsTest, NULL, testControl, NULL);
    std::cout << "create consume threads : "<< THREAD_NUM << " OK"<< std::endl;

    chrono::steady_clock::time_point t1 = chrono::steady_clock::now();

    std::cout << "join threads: start" << std::endl;
    for(int i = 0; i < THREAD_NUM; i++){
        pthread_join(threads1[i], NULL);
    }
    for(int i = 0; i < THREAD_NUM; i++){
        pthread_join(threads[i], NULL);
    }
    pthread_join(threadsTest, NULL);
    std::cout << "join threads end" << std::endl;


    chrono::steady_clock::time_point t2 = chrono::steady_clock::now();
    //毫秒级
    double dr_ms = chrono::duration<double,std::milli>(t2-t1).count();
    //微妙级
    double dr_us = chrono::duration<double,std::micro>(t2-t1).count();
    //纳秒级
    double dr_ns = chrono::duration<double,std::nano>(t2-t1).count();


    //对比enqueue 和 dequeue数据 （对比源数据矩阵和目标数据矩阵的一致性）
    for(int i = 2; i < THREAD_NUM + 2; i++){
        for(int j = 0; j < produceNUM; j++){

            for(int x = THREAD_NUM + 2; x < THREAD_NUM * 2 + 2; x++){
                for(int y = 0; y < produceNUM; y++){
                    if(s[i][j].message == s[x][y].message){
                        s[i][j].dequeueTime = s[x][y].dequeueTime;
                        s[x][y].message = 0;        //找到 清零
                        flag = 1;
                        break;
                    }
                }
                if(flag == 1) break;
            }
            flag = 0;
        }
    }

    /*检查是否有不一致*/
    flag = 0;
    for(int x = THREAD_NUM + 2; x < THREAD_NUM * 2 + 2; x++){
        for(int y = 0; y < 10; y++){
            if(0 != s[x][y].message){
                flag = 1;
                break;
            }
        }
        if(flag == 1) break;
    }
    if(flag)
        printf("message confirm result : error\n");
    else
        printf("message confirm result  :OK\n");

    //统计每一条msg的时间
    double usEnqueue;
    double usDequeue;
    double usEnqueueDequeue;

    for(int i = 2; i < THREAD_NUM + 2; i++){
        for(int j = 0; j < produceNUM; j++){
            usEnqueue = chrono::duration<double,std::milli>(s[i][j].enqueueEndTime - s[i][j].enqueueStartTime).count();
            usDequeue = chrono::duration<double,std::milli>(s[i][j].dequeueTime - s[i][j].enqueueStartTime).count();
            usEnqueueDequeue = chrono::duration<double,std::milli>(s[i][j].dequeueTime - s[i][j].enqueueEndTime).count();
        //    printf("message : %d, enqueue latency: %f transmit latency: %f\n",
        //           s[i][j].message,
        //           usEnqueue,
        //           usEnqueueDequeue);
        }
    }

    std::cout << "=================================" << std::endl;
    std::cout << "platform info:" << std::endl;
    std::cout << "cpu : Intel(R) i5-4570 CPU @ 3.20GHz cores : 4 "<< std::endl;
    std::cout << "Memory Size :10 GBytes Channels :Dual   Memory Frequency :665.1 MHz (1:5)"<< std::endl;
    std::cout << "OS: windows 7"<< std::endl;
    std::cout << "=================================" << std::endl;
    std::cout << "total message quantum : " << THREAD_NUM * produceNUM << std::endl;
    std::cout << "The run time is: " << dr_ms << " ms " <<dr_us << " us " <<dr_ns << " ns " << std::endl;
    std::cout << "the mean lantency/message is "<< dr_us/(THREAD_NUM * produceNUM) <<"us"<< std::endl;

    std::cin.get();
    return 0;
}

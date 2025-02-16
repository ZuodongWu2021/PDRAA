#include <iostream>
#include<string.h>
#include "../utility/RSA.hpp"
using namespace std;
int main()
{
    string strM;
    int p,q,e;

    cout<<"**************************************"<<endl;
    cout<<"*         简单RSA加解密程序          *"<<endl;
    cout<<"*         需输入p,q,e                *"<<endl;
    cout<<"*         p,q为质数,p*q<32767        *"<<endl;
    cout<<"*         e与fn=(p-1)*(q-1)互质      *"<<endl;
    cout<<"**************************************"<<endl;
    cout<<"请输入p:";
    cin>>p;
    while(!isPrime(p))cout<<"p非素数请重新输入:",cin>>p;
    cout<<"请输入q:";
    cin>>q;
    while(!isPrime(q))cout<<"q非素数请重新输入:",cin>>q;
    int fn = (p-1)*(q-1);
    cout<<"fn:"<<fn<<endl;
    cout<<"请输入e:";
    cin>>e;
    while(!isMutuality(e,fn))cout<<"e与fn非互质重新输入:",cin>>e;
    cout<<"请输入需加密的明文:";
    cin>>strM;

    RSA(p,q,e,(char*)strM.c_str());
    DeRSA(p,q,e,strM.length());
    return 0;
}


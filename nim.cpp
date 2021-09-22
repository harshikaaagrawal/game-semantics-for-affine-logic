#include <bits/stdc++.h>
using namespace std;

int main() {
    int n;
    cin>>n;
    int p[n];
    int x = 0;
    for(int i = 0; i < n; i++)
    {
        cin>>p[i];
        x+=p[i];
    }
    
    int current_player = 0;
    
    while(x > 0)
    {
        cout<<"Player "<<current_player+1<<"\n";
        int pile, amount;
        cin>>pile>>amount;
        if(p[pile-1] >= amount)
        {
            p[pile-1]-=amount;
            x -= amount;
        }
        else
        {
            break;
        }
        current_player = abs(current_player - 1);
    }
    
    cout<<abs(current_player - 1) +1;
	return 0;
}

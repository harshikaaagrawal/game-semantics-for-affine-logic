#include <bits/stdc++.h>
using namespace std;

int other_player(int current_player)
{
    return abs(current_player - 1);
}

void game_result(int current_player)
{
    cout<<other_player(current_player)+1<<"\n";
}

void play_nim(int n, int p[], int x)
{
    int current_player = 0;
    
    while(x > 0)
    {
        cout<<"Player "<<current_player+1<<"\n";
        int pile, amount;
        cin>>pile>>amount;
        if(p[pile-1] >= amount)
        {
            p[pile-1] -= amount;
            x -= amount;
        }
        else
        {
            break;
        }
        current_player = other_player(current_player);
    }
    
    game_result(current_player);
}

void take_input()
{
    int n;
    cin>>n;
    int p[n];
    int x = 0;
    for(int i = 0; i < n; i++)
    {
        cin>>p[i];
        x+=p[i];
    }
    
    play_nim(n, p, x);
}

int main() {
    take_input();
	return 0;
}

#include <bits/stdc++.h>
using namespace std;

char board[3][3];
int current_player = 1;

void display_current_board()
{
	cout<<"\n";
	
	for(int i = 0; i < 3; i++)
	{
	    for(int j = 0; j < 3; j++)
	    {
	        cout<<board[i][j]<<" ";
	    }
	    cout<<"\n";
	}
	return;
}

bool row()
{
	for (int i = 0; i < 3; i++) {
		if (board[i][0] == board[i][1] && board[i][1] == board[i][2] && board[i][0] != ' ')
			return (true);
	}
	return (false);
}

bool column()
{
	for (int i = 0; i < 3; i++) {
		if (board[0][i] == board[1][i] && board[1][i] == board[2][i] && board[0][i] != ' ')
			return (true);
	}
	return (false);
}

bool diagonal()
{
	if (board[0][0] == board[1][1] && board[1][1] == board[2][2] && board[0][0] != ' ')
		return (true);

	if (board[0][2] == board[1][1] && board[1][1] == board[2][0] && board[0][2] != ' ')
		return (true);

	return (false);
}

int main()
{
    cout<<"TicTacToe, User vs User \n";
	cout<<"Choose a cell between 1 to 9 as shown below to play \n";
	
	for(int i = 0; i < 3; i++)
	{
	    cout<<"------------\n";
		for(int j = 0; j < 3; j++)
		{
		    cout<<(i*3)+j+1<<" | ";
			board[i][j] = ' ';
		}
		cout<<"\n";
	}
    cout<<"\n";
	int moves_played = 0, x, y, r, c;

	while (row() || column() || diagonal() == false && moves_played != 9)
	{
		if (current_player == 1)
		{
		    player1: 
		    cout<<"Player 1, enter the respective row and column to insert X\n";
			cin>>r>>c;
			if (r <= 3 && c <= 3)
			{
				if (isblank(board[r-1][c-1]))
				{
					board[r-1][c-1] = 'X';
				}
				else 
				{
					cout<<"Invalid request, cannot fill already filled position\n";
					goto player1;
				}
			}

			else
			{
				cout<<"\nInput is invalid please enter correct input\n";
				goto player1;
			}
			current_player = 2;
		}

		else if(current_player == 2)
		{
		    player2:
		    cout<<"Player 2, Enter the respective row and column to insert O\n";
			cin>>r>>c;
			if (r <= 3 && c <= 3) 
			{
				if (isblank(board[r-1][c-1]))
				{
					board[r-1][c-1] = 'O';
				}
				else
				{
					cout<<"Invalid request, cannot fill already filled position\n";
					goto player2;
				}
			}
			else
			{
				cout<<"\nInput is not valid please enter correct input\n";
				goto player2;
			}
			current_player = 1;
		}
		
		display_current_board();
		moves_played++;
	}

	if(row()|| column() || diagonal() == false && moves_played == 9)
		cout<<"It's a draw\n";
	else
	{
		if (current_player == 1)
		{
			cout<<"Player 2 has won\n";
		}
		else if (current_player == 2)
		{
			cout<<"Player 1 has won\n";
		}
	}
	return 0;
}


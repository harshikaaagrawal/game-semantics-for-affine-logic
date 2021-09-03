#include <bits/stdc++.h>
using namespace std;

bool row(char board[3][3])
{
	for (int i = 0; i < 3; i++) {
		if (board[i][0] == board[i][1] && board[i][1] == board[i][2] && board[i][0] != ' ')
			return (true);
	}
	return (false);
}

bool column(char board[3][3])
{
	for (int i = 0; i < 3; i++) {
		if (board[0][i] == board[1][i] && board[1][i] == board[2][i] && board[0][i] != ' ')
			return (true);
	}
	return (false);
}

bool diagonal(char board[3][3])
{
	if (board[0][0] == board[1][1] && board[1][1] == board[2][2] && board[0][0] != ' ')
		return (true);

	if (board[0][2] == board[1][1] && board[1][1] == board[2][0] && board[0][2] != ' ')
		return (true);

	return (false);
}

int output_board(char board[3][3])
{
    for(int i = 0; i < 3; i++)
	 {
       for(int j = 0; j < 3; j++)
	   {
             cout<<board[i][j]<<" ";
	   }
	   cout<<"\n";
	 }
}

int game_result(int current_player, char board[3][3], int moves_played)
{
    if((row(board)|| column(board) || diagonal(board)) != true && moves_played == 9)
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
}

bool make_move(char board[3][3], int current_player, int r, int c)
{
    if (r <= 3 && c <= 3)
			{
				if (isblank(board[r-1][c-1]))
				{
				    board[r-1][c-1] = (current_player == 1) ? 'X' : 'O';
				    
				    return true; 
				}
				else 
				{
					cout<<"Invalid request, cannot fill already filled position\n";
					return false;
				}
			}
	else
	{
	    cout<<"\nInput is invalid please enter correct input\n";
	    return false;
	}
}

int input_and_make_move(int current_player, char board[3][3])
{
     cout<<"Player "<< current_player<<", enter the respective row and column to insert "<<((current_player == 1) ? 'X' : 'O')<<"\n";
    int r, c;
    cin>>r>>c;
    while(!make_move(board, current_player, r, c))
    {
        cin>>r>>c;
    }
    
    return (current_player == 1) ? 2 : 1;
}

int main_game(char board[3][3])
{
    int moves_played = 0;
    cout<<"Which player going first, input 1 or 2 \n";
    int current_player;
    cin>>current_player;
    while ((row(board) || column(board) || diagonal(board)) != true && moves_played != 9)
	{
	    current_player = input_and_make_move(current_player, board);
	    cout<<"\n";
	    output_board(board);
		moves_played++;
	}
	
	game_result(current_player, board, moves_played);
}

void game_intro()
{
    cout<<"TicTacToe, User vs User \n";
	cout<<"Choose a cell between 1 to 9 as shown below to play \n";
    for(int i = 0; i < 3; i++)
	{
	    cout<<"------------\n";
		for(int j = 0; j < 3; j++)
		{
		    cout<<(i*3)+j+1<<" | ";
		}
		cout<<"\n";
	}
    cout<<"\n";
}

void initialise_board(char board[3][3])
{
	for(int i = 0; i < 3; i++)
	{
	    for(int j = 0; j < 3; j++)
	    {
	        board[i][j] = ' ';
	    }
	    
	}
}

int main()
{
	game_intro();
	char board[3][3];
	initialise_board(board);
	main_game(board);
	return 0;
}

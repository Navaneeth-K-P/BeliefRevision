from beliefBase import *
import os

if __name__ == "__main__":
    flag = 0
    c = 0
    os.system('cls')
    print("------------ Beleif Revision Agent ------------")
    bb = Belief_Base()
    print("Belief Revision Agent created")
    while flag == 0:
        if c > 0:
            print("------------ Beleif Revision Agent ------------")
        else:
            c +=1

        print("____ Menu ____")
        print("1. View Belief Base")
        print("2. View Belief Base Consequences")
        print("3. Query Belief Base")
        print("4. Revise")
        print("5. Quit")

        
        flag = 1
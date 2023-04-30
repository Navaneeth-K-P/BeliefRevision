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
        os.system('cls')
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

        k = int(input("Enter your option (1-5): "))
        os.system('cls')
        if k == 1:
            print("The current Belief Base is: ", bb.beliefBase)
        elif(k==2):
            con = bb.consequence()
            h = [ str(g) for g in con]
            print("The consequence of the current Belief base is: ", h)
        elif(k==3):
            q = input("Enter the belief to be queried: ")
            bb.query_belief(q)
        elif(k==4):
            q = input("Enter the belief to be revised: ")
            s = float(input("Enter the score of the belief: "))
            bb.revision(q,s)
        elif(k ==5):
            flag = 1
        w = input("Press enter to continue")

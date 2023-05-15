#include <stdio.h>
  
// Swap function
void swap(int *array,int i,int j){
    int temp=array[i];
      array[i]=array[j];
      array[j]=temp;
}

// A function to implement bubble sort
void bubbleSort(int arr[])
{
    int arr_size = sizeof(arr) / sizeof(arr[0]);
    int i, j;
    for (i = 0; i < arr_size; i++)
  
        // Last i elements are already 
        // in place
        for (j = 0; j < arr_size - i - 1; j++)
            if (arr[j] > arr[j + 1])
                swap(arr,j,j + 1);
}
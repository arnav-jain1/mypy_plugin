# https://stackoverflow.com/questions/66995380/target-size-and-input-size-not-matching-despite-minibatches-tells-otherwise

import torch
import torch.nn as nn
import torch.nn.functional as F

from torch.utils.data import DataLoader
import torch.optim as optim

from torchvision import datasets
import torchvision.transforms as transforms

from sklearn.model_selection import train_test_split


#################
batch_size = 64
epochs = 1
latent_dim = 64
device = "cuda"
lr = 0.1
dataroot = "../../../data"

transform = transforms.Compose([
    transforms.ToTensor(),
    lambda x: torch.reshape(x, (784,)),
])

train_set, valid_set = train_test_split(
    datasets.MNIST(root=dataroot, train=True, transform=transform, download=True),
    test_size=0.1,
)
test_set = datasets.MNIST(root=dataroot, train=False, transform=transform, download=True)
#################

train_loader = DataLoader(train_set, batch_size=batch_size, shuffle=True, drop_last=True)
valid_loader = DataLoader(valid_set, batch_size=batch_size, shuffle=True, drop_last=True)
test_loader = DataLoader(test_set, batch_size=batch_size, shuffle=True, drop_last=True)

class AE(nn.Module):
    def __init__(self,latent_dim):
        super(AE, self).__init__()
        ### Encoder layers
        self.fc_enc1 = nn.Linear(784, 32)
        self.fc_enc2 = nn.Linear(32, 16)
        self.fc_enc3 = nn.Linear(16, latent_dim)
        
        ### Decoder layers
        self.fc_dec1 = nn.Linear(latent_dim, 16)
        self.fc_dec2 = nn.Linear(16,32)
        self.fc_dec3 = nn.Linear(32,784)

    def encode(self, x):       
        z = F.relu(self.fc_enc1(x))
        z = F.relu(self.fc_enc2(z))
        z = F.relu(self.fc_enc3(z))
        
        return z

    def decode(self, z):    
        xHat = F.relu(self.fc_dec1(z))
        xHat = F.relu(self.fc_dec2(xHat))
        xHat = F.sigmoid(self.fc_dec3(xHat))

        return xHat

    def forward(self, x):
        ### Autoencoder returns the reconstruction and latent representation
        z = self.encode(x)
        
        ### decode z
        xHat = self.decode(z)
        return xHat, z 


AEmodel = AE(latent_dim).to(device)
optimizer = optim.Adam(AEmodel.parameters(), lr=lr)
loss_function = nn.BCELoss()


for epoch in range(1, epochs + 1):
    AEmodel.train()
    train_loss = 0
    for batch_idx, (data, _) in enumerate(train_loader):
        data = data.float().to(device)
        optimizer.zero_grad()
        xHat, z = AEmodel(data)
        loss = loss_function(xHat, data)
        loss.backward()
        train_loss += loss.item()
    optimizer.step()

    AEmodel.eval()
    valid_loss = 0
    with torch.no_grad():
        for i, (data, _) in enumerate(valid_loader):
            data = data.float().to(device)
            valid_loss += loss_function(xHat, data).item()